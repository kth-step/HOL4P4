structure excluded = struct

open mlibUseful;

val exclude_descs =
 [(*
    Header unions
    FAIL: Could not parse .*\/(.*?)\. Unknown declaration element type: HeaderUnion
  *)
  ("adding header unions to HOL4P4",
   ["header-bool-bmv2",
    "issue1879-bmv2",
    "issue561-1-bmv2",
    "issue561-2-bmv2",
    "issue561-3-bmv2",
    "issue561-5-bmv2",
    "issue561-4-bmv2",
    "issue561-7-bmv2",
    "issue561-6-bmv2",
    "union1-bmv2",
    "union3-bmv2",
    "union2-bmv2",
    "union-valid-bmv2",
    "union-bmv2"]),
(*
    Variable-width integers
    FAIL: Could not parse .*\/(.*?)\. .*varbit.*
*)
  ("adding dynamically-sized bit-strings to HOL4P4",
   ["checksum1-bmv2",
    "equality-varbit-bmv2",
    "equality-bmv2",
    "issue1025-bmv2",
    "issue447-1-bmv2",
    "issue447-2-bmv2",
    "issue447-3-bmv2",
    "issue447-4-bmv2",
    "issue447-bmv2",
    "issue447-5-bmv2",
    "test-parserinvalidargument-error-bmv2"]),
  (*
   Header stacks
   FAIL: Could not parse .*\/(.*?)\. .*? \["header_stack".*
  *)
  ("adding header stacks to HOL4P4",
   ["array-copy-bmv2",
    "header-stack-ops-bmv2",
    "stack_complex-bmv2",
    "runtime-index-2-bmv2",
    "subparser-with-header-stack-bmv2",
    "ternary2-bmv2"]),
(*
    Bit slice lvalues
    FAIL: Could not parse .*\/(.*?)\. .*?: \["bit_string_access".*
*)
  ("extending import tool to properly support bit slice lvalues",
   ["issue870_ebpf",
    "issue983-bmv2",
    "match-on-exprs-bmv2"]),
(*
    Struct values
    FAIL: Could not parse .*\/(.*?)\. .*list.*
*)
  ("fixing import tool to parse struct values",
   ["constant-in-calculation-bmv2",
    "issue655",
    "recursive-casts"]),
(*
    Introduction of tuple types (manually spotted)
*)
  ("adding tuple types to HOL4P4",
   ["checksum2-bmv2",
    "checksum3-bmv2"]),
(*
    Signed integers
    FAIL: Could not parse .*\/(.*?)\. .*?: \["int".*
*)
  ("adding signed integers to HOL4P4",
   ["arith5-bmv2",
    "arith1-bmv2",
    "concat-signed",
    "runtime-index-bmv2",
    (* Manually spotted *)
    "saturated-bmv2"]),
(*
    Enumeration type declarations (manually spotted)
*)
  ("adding support for enumeration type declarations in the import tool",
   ["decl-soundness",
    "enum-bmv2"]),
(*
    Register extern of V1Model (manually spotted)
*)
  ("importing more types of register extern in V1Model model",
   ["issue1814-1-bmv2",
    "issue1097-2-bmv2"]),
(*
    Counter extern of V1Model (manually spotted)
*)
  ("adding counter extern to V1Model model",
   ["issue1566-bmv2"]),
(*
    adding checksum extern functions to V1Model model
*)
  ("adding checksum extern functions to V1Model model",
   ["issue655-bmv2"]),
(*
    Return struct of table application
*)
  ("adding hit bit, action_run et.c. to table application in HOL4P4",
   ["hit_ebpf",
    "key-issue-1020_ebpf",
    "issue2153-bmv2",
    "issue2170-bmv2",
    "switch_ebpf"]),
(*
    Set expressions in select expression
    FAIL: Could not parse .*\/(.*?)\. .*?: \["range".*
*)
  ("adding set expressions in select expressions to HOL4P4",
   ["issue995-bmv2",
    "issue1000-bmv2",
    "issue-2123-2-bmv2",
    "issue-2123-3-bmv2"),
(*
    Exit statement
    FAIL: Could not parse .*\/(.*?)\. .*?: unknown statement name: exit.*
*)
  ("adding exit statement to HOL4P4",
   ["issue2225-bmv2"]),
(*
    "Don't care" (underscore) argument (manually spotted)
*)
  ("fixing don't-care function arguments in import tool",
   ["issue774-4-bmv2"]),
];

fun get_error_desc testname [] = NONE
  | get_error_desc testname (h::t) =
 if List.exists (fn el => el = testname) (snd h)
 then SOME (fst h)
 else get_error_desc testname t
;

end
