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

(**

   This module exports types and utilities to create preconditions for
   BIR expressions, blocks and subroutines.


   Usage typically involves creating a new (abstract) {!Environment.t}
   value, a Z3 context and a {!Environment.var_gen} using the utility
   functions, along with the desired post-condition and calling the
   relevant [visit_foo] function.


   The resulting precondition can then be tested for satisfiability or
   provability using the Z3 Solver module.

*)

module Bool = Z3.Boolean

module Env = Environment

module Constr = Constraint

(** Constraints that can be added to the precondition as either assumptions or
    verification conditions, and when to apply those constraints during a visit
    to an instruction. *)
type hooks = {
  assume_before : Constr.t list;
  assume_after : Constr.t list;
  verify_before : Constr.t list;
  verify_after : Constr.t list;
}

(** Create the Z3 BitVector zero value of width [i]. *)
val z3_expr_zero : Z3.context -> int -> Constr.z3_expr

(** Create the Z3 BitVector 1 value of width [i]. *)
val z3_expr_one : Z3.context -> int -> Constr.z3_expr

(** Translate a BIR binary operator to a Z3 one. *)
val binop : Z3.context -> Bap.Std.binop -> Constr.z3_expr -> Constr.z3_expr -> Constr.z3_expr

(** Translate a BIR unary operator to a Z3 one. *)
val unop : Z3.context -> Bap.Std.unop -> Constr.z3_expr -> Constr.z3_expr

(** Translate a BIR cast operation into a Z3 one. *)
val cast : Z3.context -> Bap.Std.cast -> int -> Constr.z3_expr -> Constr.z3_expr

(** Look up the precondition for a subroutine in the given environment,
    for a given postcondition. *)
val lookup_sub : Bap.Std.Label.t -> Constr.t -> Env.t -> Constr.t * Env.t

(** Get {e every} variable from a subroutine. *)
val get_vars : Env.t -> Bap.Std.Sub.t -> Bap.Std.Var.Set.t

(** Find the set of BAP variables in a subroutine for equivalence checking
    given the name of each variable. *)
val get_output_vars : Env.t -> Bap.Std.Sub.t -> string list -> Bap.Std.Var.Set.t

(** Generates a list of constraints: [var == init_var] where init_var refers to
    the initial state of the variable var. Also updates the environment to contain
    a mapping of Bap variables to their generated init variables.

    Can be used in the specs using {!Env.mk_init_var} and {!Env.get_init_var}.
    e.g. `BV.mk_ult ctx (Env.get_init_var env var) z3_var` is the constraint stating
    the value of the variable at its initial state is less than its value at the
    current state. *)
val init_vars : Bap.Std.Var.Set.t -> Env.t -> Constr.t list * Env.t

(** Create a Z3 expression that denotes a load in memory [mem] at address [addr]
    with a word size of [word_size] bits and endianness [endian]. *)
val load_z3_mem
  :  Z3.context
  -> word_size:int
  -> mem:Constr.z3_expr
  -> addr:Constr.z3_expr
  -> Bap.Std.endian
  -> Constr.z3_expr

(** Create a Z3 expression that denotes a write in memory [mem] at address [addr], writing
    the value [content] with a word size of [word_size] bits and endianness [endian]. *)
val store_z3_mem
  :  Z3.context
  -> word_size:int
  -> mem:Constr.z3_expr
  -> addr:Constr.z3_expr
  -> content:Constr.z3_expr
  -> Bap.Std.endian
  -> Constr.z3_expr

(** Translates the sort of a Z3 expression from BitVector of variable width to a Boolean. *)
val bv_to_bool : Constr.z3_expr -> Z3.context -> int -> Constr.z3_expr

(** Translate a BAP word to a Z3 BitVector expression of the same width and value. *)
val word_to_z3 : Z3.context -> Bap.Std.Word.t -> Constr.z3_expr

(** Translate a BIR expression to a Z3 expression, by a straightforward translation of the
    expression semantics, using the context for values of variables.

    Returns also the assumptions and the VCs generated by the hooks in the environment. *)
val exp_to_z3 : Bap.Std.exp -> Env.t -> Constr.z3_expr * hooks * Env.t

(** Obtains all possible registers that can be used to hold input values to a function
    call for a given architecture. *)
val input_regs : Bap.Std.Arch.t -> Bap.Std.Var.t list

(** Obtains the caller saved-registers for a given architecture. *)
val caller_saved_regs : Bap.Std.Arch.t -> Bap.Std.Var.t list

(** Obtains the callee-saved registers for a given architecture. *)
val callee_saved_regs : Bap.Std.Arch.t -> Bap.Std.Var.t list

(** This spec is used for the functions [__assert_fail] or [__VERIFIER_error]. It
    returns the precondition [false]. *)
val spec_verifier_error : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is used for assumptions made with [__VERIFIER_assume(assumption)].
    It returns a precondition of [assumption => post]. *)
val spec_verifier_assume : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is used for functions of [__VERIFIER_nondet_type], which returns a
    nondeterministic value for the type. This spec chaoses the register that holds
    the output value from the function call. *)
val spec_verifier_nondet : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is used when BAP is able to generate [arg term]s for the subroutine
    in the case when an API is specified. It creates a function symbol for
    each output register given the input registers in the form
    [func_out_reg(in_reg1, in_reg2, ...)]. *)
val spec_arg_terms : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is used when RAX or EAX is used on the left-hand side of the subroutine.
    It creates a function symbol for RAX/EAX with the input registers as arguments. *)
val spec_rax_out : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is similar to {! spec_rax_out}, but will create a function symbol
    for RAX regardless if it was used in the left-hand side of the subroutine or not.
    This spec only works for x86_64 architectures. *)
val spec_chaos_rax : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is used for x86 architectures and will create a function symbol
    for all caller-saved registers given with the input registers as arguments. *)
val spec_chaos_caller_saved : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is used for the function [__afl_maybe_log]. It chaoses the registers
    RAX, RCX, and RDX. In retrowrite, these registers are stored on the stack,
    [__afl_maybe_log] is called, and then the registers are restored. *)
val spec_afl_maybe_log : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** This spec is used to inline a function call. It calls {! visit_sub} on the
    target function being called. *)
val spec_inline :
  Bap.Std.Sub.t Bap.Std.Seq.t -> Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option

(** The default spec used when mapping subroutines to their preconditions. This
    spec sets the constraint representing the subroutine being called to true, and
    in x86 architectures, increments the value of the stack pointer on return
    by the address size. *)
val spec_default : Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec

(** The default jmp spec for handling branches in a BIR program. *)
val jmp_spec_default : Env.jmp_spec

(** A jump spec that generates constraints for reaching a program point,
    according to a map specifying whether a jump was taken or not. *)
val jmp_spec_reach : Constr.path -> Env.jmp_spec

(** The default interrupt spec for handling interrupts in a BIR program. *)
val int_spec_default : Env.int_spec

(** This spec enforces each memory read to be on a non-null address. *)
val non_null_vc : Env.exp_cond

(** This spec {e assumes} each memory read to be on a non-null address. *)
val non_null_assert : Env.exp_cond

(** This spec {e assumes} that the value of a memory read at address [a] in the
    original binary is equal to the memory read of the modified binary at address
    [a + d]. *)
val mem_read_offsets : Env.t -> (Constr.z3_expr -> Constr.z3_expr) -> Env.exp_cond

(** Constant which determines the number of loop unrollings.

    We use the default value [!num_unroll = 5]. *)
val num_unroll : int ref

(** Creates an environment with
    - an empty sequence of subroutines to initialize function specs
    - an empty sequence of subroutines to inline
    - the default list of {!Environment.fun_spec}s that summarize the precondition for a
      function call
    - the default {!Environment.jmp_spec} that summarizes the precondition at a jump
    - the default {!Environment.int_spec} that summarizes the precondition for an
      interrupt
    - an empty list of {!Environment.exp_cond}s which adds assumptions and VCs to
      the precondition as hooks on certain instructions
    - a loop unroll count of 5 for use when reaching a back edge during analysis
    - an architecture of x86_64 for architecture specific constraints and specs
    - freshening variables set to false. Should be set to true in order to represent the
      variables in the modified binary
    - the option to use all function input registers when generating function symbols
      at a call site set to true
    - the default concrete range of addresses of the stack for constraints about
      the stack: [0x00007fffffff0000, 0x00007fffffffffff]
    - the default concreate range of addresses of the heap for constraints about
      the heap: [0x0000000000000000, 0x00000000ffffffff]

    unless specified. A Z3 context and var_gen are required to generate Z3
    expressions and create fresh variables. *)
val mk_env
  :  ?subs:Bap.Std.Sub.t Bap.Std.Seq.t
  -> ?to_inline:Bap.Std.Sub.t Bap.Std.Seq.t
  -> ?specs:(Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec option) list
  -> ?default_spec:(Bap.Std.Sub.t -> Bap.Std.Arch.t -> Env.fun_spec)
  -> ?jmp_spec:Env.jmp_spec
  -> ?int_spec:Env.int_spec
  -> ?exp_conds:Env.exp_cond list
  -> ?num_loop_unroll:int
  -> ?arch:Bap.Std.Arch.t
  -> ?freshen_vars:bool
  -> ?use_fun_input_regs:bool
  -> ?stack_range:int * int
  -> ?heap_range:int * int
  -> Z3.context
  -> Env.var_gen
  -> Env.t

(** Create a precondition for a given jump expression, depending on the postcondition
    and (potentially) the preconditions for the jump targets or the loop invariants.

    We do not handle indirect jumps at all: we just return the current postcondition,
    which is unsound of course. *)
val visit_jmp : Env.t -> Constr.t -> Bap.Std.Jmp.t -> Constr.t * Env.t

(** Create a precondition for a given block element, which may be a jump, an
    assignment or a phi node. Depends on the postcondition, and the preconditions
    of other blocks or subroutines if the elt is a jump.

    Note that we are not complete for phi nodes, and
    the Z3 semantics may be weaker than the BIR semantics. *)
val visit_elt : Env.t -> Constr.t -> Bap.Std.Blk.elt -> Constr.t * Env.t

(** Create a precondition for a given block. Depends on the postcondition, and
    the preconditions of other blocks or subroutines if there is a jump.

    Currently we do not handle loops very well, except by suppressing all back-
    edges in the CFG. *)
val visit_block : Env.t -> Constr.t -> Bap.Std.Blk.t -> Constr.t * Env.t

(** Create a precondition for a given subroutine. Depends on the postcondition, and
    the preconditions of other blocks or subroutines if there is a jump.

    Currently we do not handle loops very well, except by suppressing all back-
    edges in the CFG. *)
val visit_sub : Env.t -> Constr.t -> Bap.Std.Sub.t -> Constr.t * Env.t

(** Calls Z3 to check for a countermodel for the precondition of a BIR program. If
    refute is set to false, it checks for a model instead. *)
val check : ?refute:bool -> Z3.Solver.solver -> Z3.context -> Constr.t -> Z3.Solver.status

(** Adds a constraint to the Z3 solver in which var does not equal its value from
    the original Z3 model, then runs the Z3 solver again.

    This has a side effect that updates the state of the solver. The solver's state
    can be reverted back with [Z3.Solver.pop]. *)
val exclude
  :  Z3.Solver.solver
  -> Z3.context
  -> var:Constr.z3_expr
  -> pre:Constr.t
  -> Z3.Solver.status
