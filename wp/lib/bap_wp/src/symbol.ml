(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018/2019 The Charles Stark Draper Laboratory, Inc.      *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

open !Core_kernel
open Bap.Std

module Bool = Z3.Boolean
module BV = Z3.BitVector
module Expr = Z3.Expr
module Constr = Constraint
module Pre = Precondition

include Self()

type t = string * Word.t

let build_command (filename : string) : string =
  Format.sprintf "objdump -t %s | sed '0,/SYMBOL TABLE:/d' | grep -E 'data|bss' | awk '{print $1, $NF}'" filename

let run_command (cmd : string) : string list =
  let inp = Unix.open_process_in cmd in
  let r = In_channel.input_lines inp in
  In_channel.close inp; r

let parse_result (output : string list) : t list =
  output
  |> List.sort ~compare:String.compare
  |> List.rev
  |> List.fold ~init:[]
    ~f:(fun symbols line ->
        match String.split ~on:' ' line with
        | [addr; name] ->
          let width = (String.length addr) * 4 in
          let bap_addr = Word.of_string (Format.sprintf "0x%s:%d" addr width) in
          (name, bap_addr) :: symbols
        | _ -> symbols
      )

let get_symbols (filename : string) : t list =
  filename
  |> build_command
  |> run_command
  |> parse_result

(* Converts the type of addresses in [t] from Word.t to Constr.z3_expr. *)
let addrs_to_z3 (ctx : Z3.context) (syms : t list) : (string * Constr.z3_expr) list =
  List.map syms ~f:(fun (name, addr) -> (name, Pre.word_to_z3 ctx addr))

let retrowrite_pattern (name : string) : Re__.Core.re =
  Format.sprintf "^%s(_[a-fA-F0-9]+)?$" name
  |> Re.Posix.re
  |> Re.Posix.compile

let offset_constraint ~orig:(syms_orig : t list) ~modif:(syms_mod : t list)
    (ctx : Z3.context) : Constr.z3_expr -> Constr.z3_expr =
  let syms_orig = addrs_to_z3 ctx syms_orig in
  let syms_mod = addrs_to_z3 ctx syms_mod in
  let find name_orig syms =
    List.find syms ~f:(fun (name_mod, _) ->
        Re.execp (retrowrite_pattern name_orig) name_mod)
  in
  fun addr ->
    let rec calc_offsets syms_orig offsets =
      match syms_orig with
      | (name, addr_start_orig) :: ((_, addr_end_orig) :: _ as ss) ->
        begin
          match find name syms_mod with
          | None -> calc_offsets ss offsets
          | Some (_, addr_mod) ->
            begin
              let in_range = Bool.mk_and ctx [BV.mk_ule ctx addr_start_orig addr;
                                              BV.mk_ult ctx addr addr_end_orig] in
              let diff = BV.mk_sub ctx addr_mod addr_start_orig in
              calc_offsets ss (Bool.mk_ite ctx in_range (BV.mk_add ctx addr diff) offsets)
            end
        end
      | [] | _ :: [] -> offsets
    in
    calc_offsets syms_orig addr

let get_pointer ~orig:(syms_orig : t list) ~modif:(syms_mod : t list) : Word.t -> Word.t =
  let find name_mod syms =
    List.find syms ~f:(fun (name_orig, _) ->
        Re.execp (retrowrite_pattern name_orig) name_mod)
  in
  fun addr ->
    let rec find_orig syms_mod =
      match syms_mod with
      | (name_mod, addr_start_mod) :: ((_, addr_end_mod) :: _ as ss) ->
        begin
          match find name_mod syms_orig with
          | None -> find_orig ss
          | Some (name_orig, addr_orig) ->
            if Word.(addr_start_mod <= addr && addr < addr_end_mod) then
              let diff = Word.(addr_start_mod - addr_orig) in
              let ptr = Word.(addr - diff) in
              printf "Rewriting pointer from %s:%s to %s:%s\n%!"
                name_mod (Word.to_string addr) name_orig (Word.to_string ptr);
              ptr
            else
              find_orig ss
        end
      | [] | _ :: [] -> addr
    in
    find_orig syms_mod

let update_exp ~orig:(orig : t list) ~modif:(modif : t list) (exp : Exp.t) : Exp.t =
  let open Bil.Types in
  let rec update_exp_aux exp =
    match exp with
    | Int word ->
      let word' = get_pointer ~orig ~modif word in
      Int word'
    | Load (mem, addr, endian, size) ->
      let mem' = update_exp_aux mem in
      let addr' = update_exp_aux addr in
      Load (mem', addr', endian, size)
    | Store (mem, addr, exp, endian, size) ->
      let mem' = update_exp_aux mem in
      let addr' = update_exp_aux addr in
      let exp' = update_exp_aux exp in
      Store (mem', addr', exp', endian, size)
    | BinOp (bop, x, y) ->
      let x' = update_exp_aux x in
      let y' = update_exp_aux y in
      BinOp (bop, x', y')
    | UnOp (u, x) ->
      let x' = update_exp_aux x in
      UnOp (u, x')
    | Cast (cst, i, x) ->
      let x' = update_exp_aux x in
      Cast (cst, i, x')
    | Let (v, exp, body) ->
      let exp' = update_exp_aux exp in
      let body' = update_exp_aux body in
      Let (v, exp', body')
    | Ite (cond, yes, no) ->
      let cond' = update_exp_aux cond in
      let yes' = update_exp_aux yes in
      let no' = update_exp_aux no in
      Ite(cond', yes', no')
    | Extract (high, low, exp) ->
      let exp' = update_exp_aux exp in
      Extract (high, low, exp')
    | Concat (w1, w2) ->
      let w1' = update_exp_aux w1 in
      let w2' = update_exp_aux w2 in
      Concat (w1', w2')
    | Var v ->  Var v
    | Unknown (str, typ) -> Unknown (str, typ)
  in
  update_exp_aux exp

let update_blk ~orig:(orig : t list) ~modif:(modif : t list) (blk : Blk.t) : Blk.t =
  blk
  |> Blk.elts
  |> Seq.fold ~init:blk ~f:(fun b elt ->
      match elt with
      | `Def def -> def |> Def.map_exp ~f:(update_exp ~orig ~modif) |> Term.update def_t b
      | `Jmp jmp -> jmp |> Jmp.map_exp ~f:(update_exp ~orig ~modif) |> Term.update jmp_t b
      | `Phi phi -> phi |> Phi.map_exp ~f:(update_exp ~orig ~modif) |> Term.update phi_t b)

let rewrite_pointers ~orig:(orig : t list) ~modif:(modif : t list) (sub : Sub.t) : Sub.t =
  sub
  |> Term.enum blk_t
  |> Seq.fold ~init:sub ~f:(fun s blk ->
      blk
      |> update_blk ~orig ~modif
      |> Term.update blk_t s)
