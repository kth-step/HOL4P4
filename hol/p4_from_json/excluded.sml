structure excluded = struct

(* Missing features: description, substrings of their import errors, tests excluded by name *)
val exclude_descs =
 [("adding header unions to HOL4P4",
   ["Unknown declaration element type: HeaderUnion"],
   []),
  ("adding dynamically-sized bit-strings to HOL4P4",
   ["[\"varbit\","],
   []),
  ("adding header stacks to HOL4P4",
   ["[\"header_stack\","],
   []),
  ("adding signed integers to HOL4P4",
   ["type: [\"int\",", "[\"Left\",[\"int\","],
   []),
  ("BMv2's zeroed initial register contents, which v1model.p4 leaves unspecified",
   [],
   ["issue1814-1-bmv2"]),
  ("adding if-expressions to HOL4P4",
   ["expression: [\"ternary\","],
   []),
  ("adding exit statement to HOL4P4",
   ["unknown statement name: exit"],
   [])
 ];

fun excluded_test_desc testname =
 Option.map #1 (List.find (fn (_, _, tests) => List.exists (fn t => t = testname) tests) exclude_descs);

fun excluded_error_desc msg =
 Option.map #1 (List.find (fn (_, msgs, _) => List.exists (fn m => String.isSubstring m msg) msgs) exclude_descs);

end
