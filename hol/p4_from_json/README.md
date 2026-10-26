# Import Tool

This directory contains an import tool to obtain HOL4P4 representations of P4 programs and STF specifications.
The simplest way to try this out is to use the `Makefile` in the root directory of this repository: `make validate`. You can also run `./p4_from_json.sh validate` directly from this directory.

## The `p4_from_json.sh` script

All shell-level steps of the import are subcommands of `p4_from_json.sh`, which can be run from any directory:

* `p4_from_json.sh fetch-tests [PETR4_CLONE]` copies the common include files (core.p4, v1model.p4, ebpf_model.p4 and the skeleton files) into `p4include` and the `.p4`/`.stf` test pairs into `validation_tests`, all taken from the examples of petr4 0.1.2. It reads them from an existing petr4 clone if one is given and otherwise clones a temporary copy. It adds the `static_assert` declarations of the specification's `core.p4`, which petr4's lacks, to `p4include/core.p4`.

* `p4_from_json.sh export DIR [INCLUDE_DIR]` uses petr4 to transform every `.p4` program in `DIR` to its JSON representation, with `INCLUDE_DIR` defaulting to `p4include`.

* `p4_from_json.sh convert FILE.json [--mode MODE] [--arch ARCH] [--log FILE] [--keep-info]` transforms one JSON file into a HOL4P4 `Script.sml` next to it, replacing an existing one (which is deleted first, so that a failed conversion leaves none). `MODE` is `concrete`, `stf` (concrete, with the tests of the accompanying `.stf` file) or `symbolic` (for the symbolic executor); by default `stf` is used when an `.stf` file exists and `concrete` otherwise. The architecture is detected from the package type the program instantiates (`V1Switch`, `ebpfFilter` or `VSS`) and can be overridden with `--arch vss|ebpf|v1model`. petr4's source-position fields are stripped before parsing, which makes it a lot faster; `--keep-info` keeps them. The result of every conversion is appended to the log file, by default `p4_from_json.log` in this directory.

* `p4_from_json.sh convert-dir DIR [-j N] [--mode MODE] [--log FILE] [--keep-info]` converts all JSON files in `DIR`, `N` at a time. Rule of thumb: don't use all (virtual) cores on your computer, or instability may ensue. The log is started afresh and a summary of OK, FAIL and EXCLUDED results, and of conversions that crashed without a log entry, is printed at the end.

* `p4_from_json.sh validate [-j N]` runs `export` and `convert-dir` on `validation_tests` and then compiles the result with `Holmake`. It fails unless the numbers of OK, FAIL and EXCLUDED imports are those in `VALIDATE_EXPECTED` at the top of the script: update it when a change makes the import accept or reject more tests.

## HOL4 files

`excluded.sml` lists the features HOL4P4 lacks, each with a description, substrings of the import errors the feature causes, and the names of tests that need it although their import succeeds. An import that fails with one of these errors is logged as EXCLUDED (with the description) instead of FAIL, and the named tests are not converted at all.

`parse_jsonScript.sml` is a theory of generic JSON objects.

`petr4_to_hol4p4.sml` is the internal mechanism of `p4_from_json.sh convert` that does the actual format transformation from petr4 JSON to HOL4P4; it also contains the parser for the `.stf` specification of a test (the `parse_stf` functions). `petr4_to_hol4p4Script.sml` holds the theorems needed for this, and `petr4_to_hol4p4Syntax.sml` the syntax library.

## Program transformations

In order to accommodate P4 programs in the syntax of HOL4P4, a bit of desugaring must be done.

### Generated names

P4 identifiers consist of letters, digits and `_`. Every name the import generates, except the reserved `gen_apply_result`, contains `.`, `$` or `#`, so it differs from every name in the program, and the forms below differ from each other:

| Name | Meaning |
|---|---|
| `c.x` | variable, action or table `x` of the instance `c` inlined into its parent, or of the type `c` invoked directly (`c.d.x` for nested instances); tables are also qualified by their block (`MyIngress.c.t`) |
| `s.sub.x` | state `x` of the sub-parser instance `sub` applied in state `s` |
| `s.sub$accept`, `s.sub$reject` | the states that its `accept` and `reject` lead to |
| `set_no_match$` | the target state of a select without default case |
| `from_table$`, `hit$` | the extra parameters of every action |
| `dontcare$k` | the variable for the don't-care argument at position `k` of a call |
| `x$shadow` | a local variable `x` of an apply block, renamed because a later table key uses the outer `x` |
| `fresh$` | the variable of a havoc block (`{ fresh$; v = fresh$; }`) |
| `$s.i.x` | the variable `x` declared in block `i` of parser state `s`, moved to the parser; the only names that start with `$` |
| `c#k` | in the type maps only: constructor parameter `k` of block type or instance `c`, or type parameter `k` of extern instance `c`; `#` keeps it apart from the variable `c.k` |
| `gen_apply_result` | a reserved global variable (programs that declare it are rejected) |

Inlining prefixes the generated variables of the inlined block like its other variables (`c.dontcare$1`, `c.$s.i.x`), so the names of different instances differ in the prefix; only global extern objects and `gen_apply_result` keep their names.

### Extern object instantiations

Extern objects are instantiated once, at import time, and persist across packets. Every instantiation in the program, block-local or top-level, is numbered and replaced by an assignment of the extern object reference to its variable: at the start of the block body for a block-local one, in the initial global scope for a top-level one. The import tool runs the constructor of each object once, in order, while building the initial architectural state, with the random oracle left free: contents the architecture model leaves undefined are oracle draws, as for uninitialised variables, and advance the oracle index. The first argument of the architecture's input function is the number of extern objects that persist across packets, the architecture's own fixed objects, if any, followed by these; the input function discards every extern object allocated above them, so anything a constructor allocates during a packet lives for that packet only.

### Extern calls

Every call of an extern function or extern object method must match an entry of the architecture's extern map by name and number of arguments, where the extern object and the dummy arguments added for the type arguments of `lookahead` count as arguments, and every instantiated extern object must have a constructor there; otherwise the import fails. This rejects, for example, `clone`, `truncate`, `mark_to_drop()` without argument, `packet_in.length()`, `meter` and `direct_counter` in v1model programs.

The type parameters of an extern object are bound to the type arguments of each instance, so that an integer literal passed for a parameter of type `T` of `register<bit<8>>(256) r` (as in `r.write(0, 42)`) gets width 8.

A don't-care argument `_` of a call statement becomes a fresh variable `dontcare$k` of the parameter's type, declared in a block around the call (`_` inside an expression is rejected). When the parameter's type is a type parameter of the method or function, the call must have exactly one type argument, which is taken as its type (`p.extract<H>(_)`).

`verify_checksum(c, data, hdr.h.f, algo)` with `hdr.h` a header becomes `verify_checksum(c && hdr.h.isValid(), data, hdr.h.f, algo)`, since BMv2 skips the check when the header holding the checksum field is invalid.

### Function names

The semantics resolves a call by name in the block's local functions before the global ones, also when the caller is a global function. The import therefore rejects a program in which a block-local action has the name of a global function that is called by a global function reached from the block (through the calls in the block's code and tables and in the global functions they reach), by an earlier action of the block, or by the code of an inlined block (see the taboo list below).

### Nested control blocks

The most significant program transformation concerns inlining of nested blocks. Nested control blocks work in the following manner (for nested parsers, see below):

When instantiated blocks are applied (called), the apply block (body) of the nested block is inlined in the parent block, with all variables, actions and tables prefixed with the instance name and a period (`c1.x`). The copy-in copy-out mechanism of block parameters is handled as follows:

Copy-in:
* If the parameter is `out`, then the (prefixed) parameter is havoc-ed: it is assigned a variable declared without initialiser in a fresh block, which takes an unspecified value from the random oracle (headers start invalid)
* Otherwise, assign the argument to the (prefixed) parameter.
	
Copy-out:
* If the parameter is `out` or `inout`, then assign the (prefixed) parameter to the L-value of the argument.
* Otherwise, do nothing (note that this is safe since the import tool will halt with an error if prefixed variables of the inlined programmable block intersect with those of the parent block)

Actions (local functions) of inlined blocks must be able to access the block variables of their respective block. For this reason, all block variables of the nested block are added (prefixed) to the declaration list of the parent block (as opposed to being introduced inside a block) with their copy-out L-values set to NONE. Since these are declared only once per invocation of the parent block, every inlined application starts by havoc-ing them in the same way as `out` parameters (extern objects excepted), so that no value persists between applications.

The local function maps `b_func_map` of the parent and child blocks are merged with action names prefixed in the latter, with the import tool halting with an error if name collisions are found for different entries.

After processing the entire program is complete, blocks which only occur as nested blocks will be removed from the pblock_map to avoid clutter.
	
Note that if the same block is instantiated twice, it uses different tables, while if it is instantiated once but applied twice, the same table is used. A direct type invocation (`C.apply(...)`) uses the prefix `C`, so several direct invocations of `C` in one control share one instance; the spec gives each its own, but forbids this when `C` contains controllable entities such as tables and extern objects, which the import rejects, and without these sharing is not observable.

Also, this method does not permit nested blocks from using a return statement to finish. Accordingly, the import tool halts with an error if inlining of programmable blocks with bodies containing return statements is attempted.

Control-typed constructor parameters (`control C2(inout bit<16> x)(my_control_type c)`, instantiated as `C2(c1) c2`) are supported as follows: `c.apply(...)` in the body of `C2` becomes a placeholder, replaced when `c2` is applied by the inlined apply of `c1` under the prefix `c1`, so blocks given the same instance share its tables and extern objects. A block can hand its parameter on to a nested instance (`Mid(c) m` in `C2`): the placeholder then stays until `c2` is applied. The arguments of such an apply must be variables, not literals. Constructor arguments that are instantiations (`C2(C1())`) are rejected. Constructor parameters of other types are bound per instance: for a nested instance `c1`, the parameter `k` becomes the parent block variable `c1.k`, assigned the argument at the start of the parent block; for a block in the package (`MyIngress(8w5)`), it becomes a block variable assigned at the start of the block (such a block may then occur only once in the package). Constructor parameters of parser or extern type are rejected.

The new programmable block-variables resulting from the above procedure will be added to a "taboo list" - if these are encountered among the programmable block-variables of the parent block or in any variable declaration before the inlined block, the import tool will halt with an error. The taboo list also holds the global extern objects that the inlined code uses and the global functions and actions that it calls, which keep their names when inlined: a parameter, constructor parameter, variable or local action of the parent block with the same name would capture them, so the import halts with an error instead.

### Nested parser blocks

A sub-parser application `sub.apply(...)` in a parser state `s` splits the state at the call. The first part ends with the copy-in (as for nested controls), the havoc of the sub-parser's variables, their initialisers and a transition to `s.sub.start`. The states of the sub-parser are added with the prefix `s.sub.`, and their variables and parameters with the prefix `sub.` as for controls; extern-typed parameters such as `packet_in` are replaced by the argument, which must be a variable. Their transitions to `accept` and `reject` go to the new states `s.sub$accept`, which performs the copy-out and continues with the rest of `s`, and `s.sub$reject`, which performs the copy-out and rejects. Since a sub-parser also copies out when an extract or `verify` fails, every statement of the sub-parser with an extern call is preceded by the copy-out (this is not observable otherwise). Further calls in the rest of the state are split in the same way, so one instance applied in several states gets one copy of its states per call site. The arguments are typed by the sub-parser's parameters, so they may be literals or don't-care arguments `_` (a variable `dontcare$k`, as for other calls). A direct invocation `Sub.apply(...)` of a parser type is inlined in the same way under the prefix `Sub`. Before the split, the variables declared in the blocks of the state are moved to parser variables named `$s.i.x` (variable `x` of block `i` of `s`), set where they were declared, since their scope may cross the call. A state that declares a variable named like a parameter of its parser is treated the same way, so that the copy-out, which reads the parameters, is not shadowed. Sub-parsers with extern objects, and global extern objects used by a sub-parser and shadowed by a parameter or variable of the parser, are rejected; petr4 0.1.3 does not accept conditionals in parser states.

### Table names

Tables are named by the path of control instances that applies them, as p4c does: table `t` of control `MyIngress` is `MyIngress.t`, and table `t` of an instance `c` inlined into `MyIngress` is `MyIngress.c.t`. These are the names in the control plane state, in const entries and in symbolic mode. STF files may give a name with or without the control (`add MyIngress.t ...` or `add t ...`).

### Other declarations and statements

Members of an enumeration without an underlying type are 32-bit values numbered in declaration order, and the enumeration type is `bit<32>`. `static_assert` statements are checked at import, with conditions folded as compile-time constants, and become empty statements; a false or unknown condition makes the import fail. Named arguments of the package instantiation are put in the order of the package parameters. Annotations are ignored; for `@atomic` the import log gets a WARNING line, since the concurrent semantics (`conc_red`) does not keep such blocks atomic.

### Select expressions

Select expressions with no default case will get a new default case that maps to the state `set_no_match$`, which contains only a `verify(false, error.NoMatch)` statement. The `set_no_match$` state will only appear in programs with default-less select expressions, once per parser. The members of `error` are numbered in declaration order after the seven errors of `core.p4`, which are numbered 0 to 6 as the core externs and architectures expect (`NoError` 0, `PacketTooShort` 1, `NoMatch` 2).

### Table application in expressions

To accommodate table application in expressions and their returned structs, the following can be done:

* All actions are given two additional in-directed parameters called "from_table$" and "hit$".
* An assignment is prepended to the body of all actions, which contain a conditional statement (on "from_table$") with a then-case with an assignment to "gen_apply_result", which is a global variable (the import tool disallows P4 programs to have global variables, programmable-block variables, declared variables and action arguments called "gen_apply_result").
* Actions resulting from table application pass true to "from_table$", other usages pass false. Default actions of tables pass false as argument to "hit$". Actions corresponding to table entries pass true. Action calls in the regular P4 code, including calls from other actions, pass false to both, so `action_run` is the action the table chose.
* Whenever a table application is encountered by the import tool inside an expression `e` in a statement `stmt`, the following is done:
  + A new statement `stmt1` consisting of assignment to a temporary variable `tmp1` of the sub-expression `e1` preceding the table application in evaluation order (e.g. the first operand of a binary expression, if the table application is the second), if any, is constructed.
  + Appended sequentially to `stmt1` is `stmt2`: first the apply statement corresponding to the apply expression (same arguments), then an assignment to the global variable "apply_result1" of the struct expression `{ hit : apply_result_hit ; miss : !apply_result_hit ; action_result : table_bitv }`, where `table_bitv` is the action name serialised to a bitvector based on order of declaration in the program. In case the apply expression is occupying a short-circuit position in `e`, `stmt2` is enclosed in the appropriate conditional statement on `tmp1`.
  + Inside `e`, the variable `tmp1` takes the position of `e1` and `apply_result1` that of the table application.
  + The above procedure is then followed recursively, in case the apply expression was encountered as the first operand of `e`, incrementing the indices of `apply_result` and `tmp`.
* Occurrences of the table name in the code are then serialised in the same manner as for the `apply_result` struct.

Currently, a limited version of the above transformation is performed: a single table application, which must be the first operand evaluated, in the expression of an assignment, a conditional or a switch statement (`if (!t.apply().hit)`, `if (t.apply().hit && x == 2)`). The table is applied before the statement, and its result is kept in a block-local variable named after the table. Other table applications in expressions are rejected.
Such a switch becomes a chain of conditionals: fall-through labels share the code of the next case, and the `default` case, which must come last, becomes the final else branch.

### Tables

Key expressions are resolved in the scope of the table declaration: a local variable of the apply block that shadows a variable used in a key of a later table application is renamed by appending `$shadow`.

Constant entries of a table with only exact and LPM keys are matched by longest prefix (an `@priority` annotation is ignored, as BMv2 does). In other tables the smallest `@priority` wins, an entry without annotation having its position (counted from 1) as priority, as p4c gives them; the architecture models take the smallest priority in such tables, as BMv2 does.

The arguments of default actions and of constant entries are folded to values at import; arguments that do not fold are rejected. A table without `default_action` gets `NoAction`, which is then also listed among the table's actions. The import rejects arguments bound in a table's actions list (directional action parameters). The order in which matching entries win is fixed by the architecture model, so the import rejects the table properties `largest_priority_wins` and `priority_delta`.

### Other rejected forms

The import also rejects default parameter values, `==` and `!=` on structs, headers and tuples, a parser or control type with tables, extern objects or constructor parameters passed twice to the package (its instances would share them), a block variable named like a constructor parameter, `verify` outside parsers, serializable enum members whose value does not fit the type, and a control type with tables or extern objects invoked directly (`C.apply(...)`) more than once in a control, whose invocations would share them. Integer constant expressions are folded exactly (negative intermediates included) and then take the expected width; comparisons of integer constants fold to booleans. Bitwise operators are not defined on two integer constants (spec 8.8, and petr4 rejects them), and a shift of an integer constant by a non-constant amount is rejected. Constants may use unary operators and struct initialisers.

### Compile-time constants

Widths and slice bounds are folded exactly at import: `int` arithmetic is exact, a `bit<W>` operand or width-prefixed literal wraps modulo 2^W (`bit<(4w15 + 4w2)>` is `bit<1>`), `&`, `|`, `^` and `~` fold on `bit<W>` operands, and global `bit<W>` constants may occur in slice bounds (`x[HI:0]`) and in the widths of fields, typedefs, variables, constants and casts (`bit<(W)>`), but not of parameters; a negative result is rejected. A width-prefixed literal that overflows its width wraps (`8w300` is `44`). `minSizeInBits()` and `minSizeInBytes()` fold to the size of the receiver's type. Constants of type `int` are not supported.

### Struct initialisers

A list expression `{e1, ..., en}` of struct type becomes a struct with the declared field names, and a structure-valued expression `{f = e, ...}` a struct with its fields in declaration order. Both are rejected at header type, since HOL4P4 has no header-valued expressions. A list expression without a known struct type is a tuple with fields `"1"`..`"n"`.

### VSS

VSS programs must include the VSS model of section 5.1 of the P4 specification, which names the checksum extern `Checksum16`, as the HOL4P4 VSS model does; petr4's `very_simple_model.p4` names it `Ck16`. The packet arguments of the parser and the deparser become the model's `b_in` and `b_out`.

## STF files

`parse_stf` in `petr4_to_hol4p4.sml` reads the `packet`, `expect`, `add`, `setdefault` and `wait` commands of an STF file, as p4c's STF test drivers do, and fails on any other command. The keys of `add` are matched to the table's keys by name: the name of a key is its `@name` annotation or its expression (`hdr.h.a`), and an STF key name matches it when one extends the other by a prefix (`h.a` matches `hdr.h.a`); eBPF keys can also be given as `key.fieldN`. A key value is a number (decimal, `0x` hexadecimal or `0b` binary), a number with `*` for don't-care digits, `value&&&mask` or `value/prefix_length`; boolean keys take 0 or 1. Keys left out match anything, except exact keys, which must be given. Action arguments are matched to the action's parameters by name. The key and argument types of a table or action of an inlined instance (`MyIngress.c.t`, `MyIngress.c.set`) are those of the instance's control type. In a table with only exact and LPM keys, the longest prefix wins and the priority in the `add` command is ignored; in other tables the largest STF priority wins, as in p4c's BMv2 STF driver, which passes 10000 minus it to BMv2.

Table updates take effect for the packets after them: a table update after a packet starts a new phase, and the test theorem has one run per phase, each ending at block index 0 with no frames left. The first run starts from the configured initial state; each later one starts from the final state of the previous run, with the phase's entries added (`add_ctrl_list_gen`) and its packets as input, and with the phase's default actions set in its own `actx`. The output of the last run must be the expected packets. A file without table updates after packets gives a single run. The theorem is proved by `p4_eval_test_tac` in `hol/p4_testLib.sml`.

## How to debug a conversion

To find where a conversion fails, convert the program's top-level declarations one at a time in a `hol --holstate=p4_from_json-heap` session (started in this directory):
```
open parse_jsonTheory petr4_to_hol4p4Theory petr4_to_hol4p4Syntax;
val json_tm = stringLib.fromMLstring $ TextIO.inputAll $ TextIO.openIn "validation_tests/NAME.json";
val parse_thm = EVAL ``parse (OUTL (lex (^json_tm) ([]:token list))) [] T``;
val elems = dest_SOME_msg $ rhs $ concl $ EVAL ``p4_from_json_preamble ^(rhs $ concl parse_thm)``;
(* The state after the first n declarations, and declaration n itself *)
val n = ``4:num``;
val state = rhs $ concl $ EVAL ``petr4_parse_elements (TAKE ^n ^elems) (SOME (arch_v1model NONE))``;
val elem = rhs $ concl $ EVAL ``EL ^n ^elems``;
```
`state` is `SOME_dbg` of the parser state (or `NONE_dbg` of the state and the error message). Apply `petr4_parse_element` to it and `elem` with `EVAL`, or take its components apart with `pairSyntax.spine_pair` and evaluate the parser of the failing declaration kind (`petr4_parse_control`, `petr4_parse_actiondef`, ...) on them to narrow the error down further. Lexing is much faster on a JSON file without petr4's source-position fields, as `p4_from_json.sh convert` produces internally (see `strip_info` in `petr4_to_hol4p4.sml`).

## How to debug test files

Use `debug_arch_from_step`:
```
 val ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), ((i, in_out_list, in_out_list', ascope), g_scope_list, arch_frame_list, status)) = debug_arch_from_step "text_arch" test_name_actx test_name_astate nsteps
```

## Adding your own tests
Before performing the steps below, make sure you have ran `make hol && cd hol/p4_from_json && Holmake` in the `HOL4P4` directory to compile the necessary theories (alternatively, `make validate`, which will also run the tests).

Adding your own tests in the same style as HOL4P4’s validation tests is simple. To do so, start by taking the P4 program you would want to test and place it in `hol/p4_from_json/user_tests`. For example, take `hol/p4_from_json/validation_tests/arith2-bmv2.p4` with some small modification. Then, you need to add a STF specification (see e.g. `hol/p4_from_json/validation_tests/arith2-bmv2.stf`):

```
# header = { bit<32> a; bit<32> b; bit<8> c; }
# In the output C = A < B

packet 0 00000000 00000001 00
expect 0 00000000 00000001 01

packet 0 00000000 00000000 00
expect 0 00000000 00000000 00

packet 0 00000001 00000000 00
expect 0 00000001 00000000 00

packet 0 00000001 00000002 00
expect 0 00000001 00000002 01

packet 0 00000011 00000022 00
expect 0 00000011 00000022 01

packet 0 FFFFFFFF 00000001 00
expect 0 FFFFFFFF 00000001 00

packet 0 FFFFFFFF FFFFFFFE 00
expect 0 FFFFFFFF FFFFFFFE 00
```

Here, `packet` signifies the incoming packet and `expect` the outgoing one, with the first 0 after each of these commands being the port number. You may use * for wildcard bits in both input and output. As in p4c's STF runner, an expected packet only has to be a prefix of the output packet, unless it ends with `$`. Adapt as needed for your program, copy the `Holmakefile` from `hol/p4_from_json/validation_tests/` to `hol/p4_from_json/user_tests`, and then run

```
./p4_from_json.sh export user_tests

./p4_from_json.sh convert-dir user_tests
```

in the `hol/p4_from_json` directory, generating the .sml file (note that hyphens in the .p4 file name will also be replaced with underscores). `convert-dir` takes `-j N` to perform `N` conversions in parallel, in case you have extra horsepower to spare. To compile the test, then run

	cd user_tests && Holmake arith2_bmv2Theory
