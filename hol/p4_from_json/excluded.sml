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
    Tuple types (manually spotted)
*)
  ("desugaring tuple types in import tool",
   ["constant-in-calculation-bmv2",
    "checksum2-bmv2",
    "checksum3-bmv2",
    "issue655-bmv2"]),
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
    To-bool cast (manually spotted)
*)
  ("supporting to-bool cast in HOL4P4",
   ["issue1814-1-bmv2"]),
(*
    To-struct cast (manually spotted)
*)
  ("supporting to-struct cast in HOL4P4",
   ["recursive-casts"]),
(*
    Top-level extern instantiations (manually spotted)
*)
  ("supporting top-level extern instantiations in import tool",
   ["issue1097-2-bmv2"]),
(*
    Counter extern of V1Model (manually spotted)
*)
  ("adding counter extern to V1Model model",
   ["issue1566-bmv2"]),
(*
    Return struct of table application
*)
  ("adding support for desugaring more table application expressions to import tool",
   ["hit_ebpf",
    "key-issue-1020_ebpf",
    "switch_ebpf"]),
(*
    Set expressions in select expression
    FAIL: Could not parse .*\/(.*?)\. .*?: \["range".*
*)
  ("adding set expressions in select expressions to HOL4P4",
   ["issue995-bmv2",
    "issue1000-bmv2",
    "issue-2123-2-bmv2",
    "issue-2123-3-bmv2"]),
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
   ["issue774-4-bmv2"])
];

fun get_error_desc testname [] = NONE
  | get_error_desc testname (h::t) =
 if List.exists (fn el => el = testname) (snd h)
 then SOME (fst h)
 else get_error_desc testname t
;

end
