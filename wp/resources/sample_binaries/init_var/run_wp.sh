set -x

compile () {
  make
}

run () {
  bap main --pass=wp \
    --wp-postcond="(assert (= RAX (bvadd init_RDI #x0000000000000001)))" \
    --wp-function="foo"
}

compile && run
