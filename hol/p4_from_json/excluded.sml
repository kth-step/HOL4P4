structure excluded = struct

open mlibUseful;

val exclude_descs =
 [(*
   Header stacks
   FAIL: Could not parse .*\/(.*?)\. .*? \["header_stack".*
  *)
  ("adding header stacks to HOL4P4",
   ["alias",
    "array_field",
    "array_field1",
    "array-copy-bmv2",
    "complex2",
    "index",
    "inline-parser",
    "header-stack-ops-bmv2",
    "inline-stack-bmv2",
    "issue1406",
    "issue1409-bmv2",
    "issue1607-bmv2",
    "issue2090",
    "issue313_1",
    "issue313_2",
    "issue314",
    "issue692-bmv2",
    "issue887",
    "issue891-bmv2",
    "mask",
    "pvs-bitstring-bmv2",
    "pvs-struct-2-bmv2",
    "pvs-struct-3-bmv2",
    "side_effects",
    "runtime-index-2-bmv2",
    "spec-ex09",
    "spec-ex20",
    "spec-ex19",
    "stack2",
    "stack",
    "stack_ebpf",
    "stack-bmv2",
    "stack_complex-bmv2",
    "stack-bvec-bmv2",
    "subparser-with-header-stack-bmv2",
    "uninit",
    "ternary2-bmv2"]),
(*
    Lists
    FAIL: Could not parse .*\/(.*?)\. .*list.*
*)
  ("treatment of list expressions",
   ["assign",
    "copy",
    "constant-in-calculation-bmv2",
    "default",
    "issue1079-bmv2",
    "issue1210",
    "issue134-bmv2",
    "issue1863",
    "issue2036-3",
    "issue2265-1",
    "issue232-bmv2",
    "issue249",
    "issue270-bmv2",
    "issue430-bmv2",
    "issue529",
    "issue655-bmv2",
    "issue655",
    "issue933-1",
    "issue933",
    "issue841",
    "issue995-bmv2",
    "names",
    "nested_select",
    "select-struct",
    "spec-ex14",
    "specialization",
    "struct_init"]),
(*
    Header unions
    FAIL: Could not parse .*\/(.*?)\. Unknown declaration element type: HeaderUnion
*)
  ("adding header unions to HOL4P4",
   ["bvec_union-bmv2",
    "declarations",
    "header",
    "header-bool-bmv2",
    "issue1897-bmv2",
    "issue1879-bmv2",
    "issue561-1-bmv2",
    "issue561-2-bmv2",
    "issue561-3-bmv2",
    "issue561",
    "issue561-5-bmv2",
    "issue561-4-bmv2",
    "issue561-7-bmv2",
    "issue561-6-bmv2",
    "issue982",
    "spec-ex10",
    "spec-ex29",
    "union-key",
    "union1-bmv2",
    "union3-bmv2",
    "union2-bmv2",
    "union-bmv2",
    "union4-bmv2",
    "union-valid-bmv2"]),
(*
    Casts
    FAIL: Could not parse .*\/(.*?)\. .*cast.*
*)
  ("adding casts to HOL4P4",
   ["arith2-bmv2",
    "arith-inline-bmv2",
    "arith4-bmv2",
    "arith3-bmv2",
    "arith-bmv2",
    "bool_cast",
    "bitwise-cast",
    "direct-action1",
    "direct-action",
    "hash-bmv2",
    "initializer",
    "issue1097-2-bmv2",
    "issue1566-bmv2",
    "issue1566",
    "issue1713-bmv2",
    "issue2104",
    "issue2151",
    "issue2335-1",
    "issue584-1",
    "spec-ex25",
    "strength6",
    "strength3",
    "useless-cast"]),
(*
    Variable-width integers
    FAIL: Could not parse .*\/(.*?)\. .*varbit.*
*)
  ("adding dynamically-sized bit-strings to HOL4P4",
   ["annotation-bug",
    "checksum1-bmv2",
    "crash-typechecker",
    "equality",
    "equality-varbit-bmv2",
    "equality-bmv2",
    "issue1025-bmv2",
    "issue1291-bmv2",
    "issue1560-bmv2",
    "issue1765-bmv2",
    "issue447-1-bmv2",
    "issue447-2-bmv2",
    "issue447-3-bmv2",
    "issue447-4-bmv2",
    "issue447-bmv2",
    "issue447-5-bmv2",
    "issue561-bmv2",
    "match",
    "spec-ex08",
    "spec-ex18",
    "test-parserinvalidargument-error-bmv2"]),
(*
    Serializable enumeration types
    FAIL: Could not parse .*\/(.*?)\. Unknown declaration element type: SerializableEnum
*)
  ("adding serializable enumeration types to HOL4P4",
   ["cast-senum-senum",
    "cast-senum",
    "issue1653-complex-bmv2",
    "register-serenum",
    "serenum-casts",
    "serenum-signed",
    "serenum",
    "table-entries-ser-enum-bmv2",
    "table-key-serenum",
    "v1model-digest-containing-ser-enum"])];

fun get_error_desc testname [] = NONE
  | get_error_desc testname (h::t) =
 if List.exists (fn el => el = testname) (snd h)
 then SOME (fst h)
 else get_error_desc testname t
;

end
