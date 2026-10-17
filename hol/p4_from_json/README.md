# Import Tool

This directory contains an import tool to obtain HOL4P4 representations of P4 programs and STF specifications.
The simplest way to try this out is to use the `Makefile` in the root directory of this repository: `make validate`. You can also run `./p4_from_json.sh validate` directly from this directory.

## The `p4_from_json.sh` script

All shell-level steps of the import are subcommands of `p4_from_json.sh`, which can be run from any directory:

* `p4_from_json.sh fetch-tests [PETR4_CLONE]` copies the common include files (core.p4, v1model.p4, ebpf_model.p4 and the skeleton files) into `p4include` and the `.p4`/`.stf` test pairs into `validation_tests`, all taken from the examples of petr4 0.1.2. It reads them from an existing petr4 clone if one is given and otherwise clones a temporary copy.

* `p4_from_json.sh export DIR [INCLUDE_DIR]` uses petr4 to transform every `.p4` program in `DIR` to its JSON representation, with `INCLUDE_DIR` defaulting to `p4include`.

* `p4_from_json.sh convert FILE.json [--mode MODE] [--arch ARCH] [--log FILE] [--keep-info]` transforms one JSON file into a HOL4P4 `Script.sml` next to it. `MODE` is `concrete`, `stf` (concrete, with the tests of the accompanying `.stf` file) or `symbolic` (for the symbolic executor); by default `stf` is used when an `.stf` file exists and `concrete` otherwise. The architecture is detected from the package type the program instantiates (`V1Switch`, `ebpfFilter` or `VSS`) and can be overridden with `--arch vss|ebpf|v1model`. petr4's source-position fields are stripped before parsing, which makes it a lot faster; `--keep-info` keeps them. The result of every conversion is appended to the log file, by default `p4_from_json.log` in this directory.

* `p4_from_json.sh convert-dir DIR [-j N] [--mode MODE] [--log FILE] [--keep-info]` converts all JSON files in `DIR`, `N` at a time. Rule of thumb: don't use all (virtual) cores on your computer, or instability may ensue. The log is started afresh and a summary of OK, FAIL and EXCLUDED results is printed at the end.

* `p4_from_json.sh validate [-j N]` runs `export` and `convert-dir` on `validation_tests` and then compiles the result with `Holmake`.

## HOL4 files

`excluded.sml` contains a list of tuples of categories (categorized by what blocks them from being parsed, as a string description) of tests and the test names themselves. Used to not waste time trying to re-transform tests you know will fail.

`parse_jsonScript.sml` is a theory of generic JSON objects.

`petr4_to_hol4p4.sml` is the internal mechanism of `p4_from_json.sh convert` that does the actual format transformation from petr4 JSON to HOL4P4; it also contains the parser for the `.stf` specification of a test (the `parse_stf` functions). `petr4_to_hol4p4Script.sml` holds the theorems needed for this, and `petr4_to_hol4p4Syntax.sml` the syntax library.

## Program transformations

In order to accommodate P4 programs in the syntax of HOL4P4, a bit of desugaring must be done.

### Extern object instantiations

Extern objects are instantiated once, at import time, and persist across packets. Every instantiation in the program, block-local or top-level, is numbered and replaced by an assignment of the extern object reference to its variable: at the start of the block body for a block-local one, in the initial global scope for a top-level one. The import tool runs the constructor of each object once, in order, while building the initial architectural state, with the random oracle left free: contents the architecture model leaves undefined are oracle draws, as for uninitialised variables, and advance the oracle index. The first argument of the architecture's input function is the number of extern objects that persist across packets, the architecture's own fixed objects, if any, followed by these; the input function discards every extern object allocated above them, so anything a constructor allocates during a packet lives for that packet only.

### Nested control blocks

The most significant program transformation concerns inlining of nested blocks. Currently, only nested control blocks are supported and not nested parser blocks. This works in the following manner:

When instantiated blocks are applied (called), the apply block (body) of the nested block is inlined in the parent block, with all variables and tables prefixed with the instance name. The copy-in copy-out mechanism of block parameters is handled as follows:

Copy-in:
* If the parameter is `out`, then the (prefixed) parameter is havoc-ed (by using `arb_from_tau` to assign a value with all bits as `ARB`s to it)
* Otherwise, assign the argument to the (prefixed) parameter.
	
Copy-out:
* If the parameter is `out` or `inout`, then assign the (prefixed) parameter to the L-value of the argument.
* Otherwise, do nothing (note that this is safe since the import tool will halt with an error if prefixed variables of the inlined programmable block intersect with those of the parent block)

Actions (local functions) of inlined blocks must be able to access the block variables of their respective block. For this reason, all block variables of the nested block are added (prefixed) to the declaration list of the parent block (as opposed to being introduced inside a block) with their copy-out L-values set to NONE.

The local function maps `b_func_map` of the parent and child blocks are merged with action names prefixed in the latter, with the import tool halting with an error if name collisions are found for different entries.

After processing the entire program is complete, blocks which only occur as nested blocks will be removed from the pblock_map to avoid clutter.
	
Note that if the same block is instantiated twice, it uses different tables, while if it is instantiated once but applied twice, the same table is used.

Also, this method does not permit nested blocks from using a return statement to finish. Accordingly, the import tool halts with an error if inlining of programmable blocks with bodies containing return statements is attempted.

The new programmable block-variables resulting from the above procedure will be added to a "taboo list" - if these are encountered among the programmable block-variables of the parent block or in any variable declaration before the inlined block, the import tool will halt with an error.

### Select expressions

Select expressions with no default case will get a new default case that maps to the state `set_no_match`, which contains only a `verify(false, error.NoMatch)` statement. The import tool will halt with an error if `set_no_match` is encountered among the regular states of the P4 program. The `set_no_match` state will only appear in programs with default-less select expressions.

### Table application in expressions

To accommodate table application in expressions and their returned structs, the following can be done:

* All actions are given two additional in-directed parameters called "from_table" and "hit". The import tool disallows P4 programs with actions with pre-existing parameters named "from_table" and "hit".
* An assignment is prepended to the body of all actions, which contain a conditional statement (on "from_table") with a then-case with an assignment to "gen_apply_result", which is a global variable (the import tool disallows P4 programs to have global variables, programmable-block variables, declared variables and action arguments called "gen_apply_result").
* Actions resulting from table application pass true to "from_table", other usages pass false. Default actions of tables pass false as argument to "hit". Actions corresponding to table entries pass true. Action calls in the regular P4 code pass `ARB`.
* Whenever a table application is encountered by the import tool inside an expression `e` in a statement `stmt`, the following is done:
  + A new statement `stmt1` consisting of assignment to a temporary variable `tmp1` of the sub-expression `e1` preceding the table application in evaluation order (e.g. the first operand of a binary expression, if the table application is the second), if any, is constructed.
  + Appended sequentially to `stmt1` is `stmt2`: first the apply statement corresponding to the apply expression (same arguments), then an assignment to the global variable "apply_result1" of the struct expression `{ hit : apply_result_hit ; miss : !apply_result_hit ; action_result : table_bitv }`, where `table_bitv` is the action name serialised to a bitvector based on order of declaration in the program. In case the apply expression is occupying a short-circuit position in `e`, `stmt2` is enclosed in the appropriate conditional statement on `tmp1`.
  + Inside `e`, the variable `tmp1` takes the position of `e1` and `apply_result1` that of the table application.
  + The above procedure is then followed recursively, in case the apply expression was encountered as the first operand of `e`, incrementing the indices of `apply_result` and `tmp`.
* Occurrences of the table name in the code are then serialised in the same manner as for the `apply_result` struct.

Currently, a limited version of the above transformation is performed which only supports single table applications inside the expression of switch statements.

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

Here, `packet` signifies the incoming packet and `expect` the outgoing one, with the first 0 after each of these commands being the port number. You may use * for wildcard bits in both input and output. Adapt as needed for your program, copy the `Holmakefile` from `hol/p4_from_json/validation_tests/` to `hol/p4_from_json/user_tests`, and then run

```
./p4_from_json.sh export user_tests

./p4_from_json.sh convert-dir user_tests
```

in the `hol/p4_from_json` directory, generating the .sml file (note that hyphens in the .p4 file name will also be replaced with underscores). `convert-dir` takes `-j N` to perform `N` conversions in parallel, in case you have extra horsepower to spare. To compile the test, then run

	cd user_tests && Holmake arith2_bmv2Theory
