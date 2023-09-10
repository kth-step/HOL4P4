structure excluded = struct

open mlibUseful;

val exclude_descs =
 [(*
    Header unions
    FAIL: Could not parse .*\/(.*?)\. Unknown declaration element type: HeaderUnion
  *)
  ("adding header unions to HOL4P4",
   [(* With STF: *)
    "header-bool-bmv2",
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
    "union-bmv2",
    (* Without STF: *)
    "bvec_union-bmv2",
    "declarations",
    "header",
    "issue1897-bmv2",
    "issue561",
    "issue982",
    "spec-ex10",
    "spec-ex29",
    "union-key",
    "union4-bmv2"]),
(*
    Variable-width integers
    FAIL: Could not parse .*\/(.*?)\. .*varbit.*
*)
  ("adding dynamically-sized bit-strings to HOL4P4",
   [(* With STF: *)
    "checksum1-bmv2",
    "equality-varbit-bmv2",
    "equality-bmv2",
    "issue1025-bmv2",
    "issue447-1-bmv2",
    "issue447-2-bmv2",
    "issue447-3-bmv2",
    "issue447-4-bmv2",
    "issue447-bmv2",
    "issue447-5-bmv2",
    "test-parserinvalidargument-error-bmv2",
    (* Without STF: *)
    "annotation-bug",
    "crash-typechecker",
    "equality",
    "issue1291-bmv2",
    "issue1560-bmv2",
    "issue1765-bmv2",
    "issue561-bmv2",
    "match",
    "spec-ex08",
    "spec-ex18"]),
  (*
   Header stacks
   FAIL: Could not parse .*\/(.*?)\. .*? \["header_stack".*
  *)
  ("adding header stacks to HOL4P4",
   [(* With STF: *)
    "array-copy-bmv2",
    "header-stack-ops-bmv2",
    "stack_complex-bmv2",
    "runtime-index-2-bmv2",
    "subparser-with-header-stack-bmv2",
    "ternary2-bmv2",
    (* Without STF: *)
    "alias",
    "array_field",
    "array_field1",
    "complex2",
    "index",
    "inline-parser",
    "inline-stack-bmv2",
    "issue1406",
    "issue1409-bmv2",
    "issue1607-bmv2",
    "issue1989-bmv2.json",
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
    "spec-ex09",
    "spec-ex20",
    "spec-ex19",
    "stack2",
    "stack",
    "stack_ebpf",
    "stack-bmv2",
    "stack-bvec-bmv2",
    "uninit"]),
(*
    Bit string access
    FAIL: Could not parse .*\/(.*?)\. .*?: \["bit_string_access".*
*)
  ("extending JSON-to-HOL4P4 parser to properly support bit string access",
   [(* With STF: *)
    "issue870_ebpf",
    "issue983-bmv2",
    "issue2343-bmv2",
    "match-on-exprs-bmv2"]),
(*
    Lists
    FAIL: Could not parse .*\/(.*?)\. .*list.*
*)
  ("treatment of list expressions",
   [(* With STF: *)
    "constant-in-calculation-bmv2",
    "issue655",
    "issue995-bmv2",
    (* Without STF: *)
    "assign",
    "copy",
    "default",
    "issue1079-bmv2",
    "issue1210",
    "issue134-bmv2",
    "issue1863",
    "issue2036-3",
    "issue2261.json",
    "issue2265-1",
    "issue2289.json",
    "issue232-bmv2",
    "issue249",
    "issue270-bmv2",
    "issue430-1-bmv2.json",
    "issue430-bmv2",
    "issue529",
    "issue655-bmv2",
    "issue933-1",
    "issue933",
    "issue841",
    "names",
    "nested_select",
    "select-struct",
    "spec-ex14",
    "specialization",
    "struct_init"]),
(*
    Match kind
    FAIL: Could not parse .*\/(.*?)\. .*? could not parse match kind.*
*)
  ("supporting introduction of new match kinds",
   [(* With STF: *)
    "table-entries-optional-bmv2",
    "table-entries-range-bmv2",
    (* Without STF: *)
    "action_profile_max_group_size_annotation.json",
    "action_profile-bmv2.json",
    "action_selector_shared-bmv2.json",
    "issue297-bmv2.json"]),
(*
    Serializable enumeration types
    FAIL: Could not parse .*\/(.*?)\. Unknown declaration element type: SerializableEnum
*)
  ("adding serializable enumeration types to HOL4P4",
   [(* With STF: *)
    "cast-senum",
    "table-entries-ser-enum-bmv2",
    (* Without STF: *)
    "cast-senum-senum",
    "issue1653-complex-bmv2",
    "register-serenum",
    "serenum-casts",
    "serenum-signed",
    "serenum",
    "table-key-serenum",
    "v1model-digest-containing-ser-enum"]),
(*
    Signed integers
    FAIL: Could not parse .*\/(.*?)\. .*?: \["int".*
*)
  ("adding signed integers to HOL4P4",
   [(* With STF: *)
    "arith5-bmv2",
    "arith1-bmv2",
    "concat-signed",
    "runtime-index-bmv2",
    (* Manually spotted *)
    "saturated-bmv2"]),
(*
    Nested control blocks (manually spotted)
*)
  ("adding nested control blocks to HOL4P4",
   [(* With STF: *)
    "arith-inline-bmv2",
    "arith2-inline-bmv2",
    "default_action-bmv2",
    "key-bmv2",
    "two_ebpf"]),
(*
    Register extern (manually spotted)
*)
  ("adding register extern to HOL4P4",
   [(* With STF: *)
    "issue1814-1-bmv2"]),
(*
    Counter extern (manually spotted)
*)
  ("adding counter extern to HOL4P4",
   [(* With STF: *)
    "issue1566-bmv2"]),
(*
    CounterArray extern (manually spotted)
*)
  ("adding counter array extern to HOL4P4",
   [(* With STF: *)
    "count_ebpf",
    "valid_ebpf"]),
(*
    Better support for enumeration types (manually spotted)
*)
  ("extending JSON-to-HOL4P4 parser to more properly support enumeration types",
   [(* With STF: *)
    "decl-soundness",
    "enum-bmv2"]),
(*
    Hit bit of table (manually spotted)
*)
  ("adding hit bit of tables to HOL4P4",
   [(* With STF: *)
    "hit_ebpf",
    "key-issue-1020_ebpf"]),
(*
    Switch statement
    FAIL: Could not parse .*\/(.*?)\. .*?: unknown statement name: switch.*
*)
  ("adding switch statement to HOL4P4",
   [(* With STF: *)
    "issue2153-bmv2",
    "issue2170-bmv2",
    "switch_ebpf"]),
(*
    Range expressions
    FAIL: Could not parse .*\/(.*?)\. .*?: \["range".*
*)
  ("adding range expressions to HOL4P4",
   [(* With STF: *)
    "issue-2123-2-bmv2"]),
(*
    Exit statement
    FAIL: Could not parse .*\/(.*?)\. .*?: unknown statement name: exit.*
*)
  ("adding exit statement to HOL4P4",
   [(* With STF: *)
    "issue2225-bmv2"]),
(*
    (Nested) struct values (manually spotted)
*)
  ("adding more proper support for struct values to HOL4P4",
   [(* With STF: *)
    "recursive-casts"]),
(*
    Bit masks
    FAIL: Could not parse .*\/(.*?)\. .*?: \["mask".*
*)
  ("adding bit masks to HOL4P4",
   [(* With STF: *)
    "table-entries-exact-ternary-bmv2",
    "table-entries-lpm-bmv2",
    "table-entries-priority-bmv2",
    "table-entries-ternary-bmv2",
    "v1model-const-entries-bmv2"]),
(*
    Saturated subtraction (manually spotted)
*)
  ("adding saturated subtraction to HOL4P4",
   [(* With STF: *)
    "issue2287-bmv2"]),
(*
    "Don't care" (underscore) lval (manually spotted)
*)
  ("adding don't-care-lval to HOL4P4",
   [(* With STF: *)
    "issue774-4-bmv2"]),
(*
    Permitting more free expressions as table keys (manually spotted)
*)
  ("extending HOL4P4 to allow more expressions as table keys",
   [(* With STF: *)
    "issue1000-bmv2",
    "issue-2123-3-bmv2"])
];

fun get_error_desc testname [] = NONE
  | get_error_desc testname (h::t) =
 if List.exists (fn el => el = testname) (snd h)
 then SOME (fst h)
 else get_error_desc testname t
;

end
