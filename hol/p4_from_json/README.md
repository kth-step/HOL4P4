# Import Tool

This directory contains an import tool to obtain HOL4P4 representations of P4 programs and STF specifications.
The simplest way to try this out is to use the `Makefile` in the root directory of this repository: `make validate`. You can also run them directly from this directory via `.validate.sh`.

## Shell scripts

`petr4_json_export.sh` uses petr4 to transform .p4 programs to JSON. It takes a path to a directory with .p4 programs and a path to common includes (e.g. architecture descriptions such as v1model.p4, ...) as command line arguments and will transform all .p4 programs found to .json representation.

`strip_json_info.sh` takes a file name as a command-line argument and tries to remove debug information from the JSON in the file, shrinking the size of the .json considerably.

`petr4_to_hol4p4.sh` takes a path and a log file as command-line arguments and tries to transform all .json files found in the path into HOL4P4 .sml files. This uses a hard-coded remove_debug flag to decide whether the `strip_json_info.sh` script will be used on all .json files involved.

`petr4_to_hol4p4_dir.sh` is the version of `petr4_to_hol4p4.sh` for entire directories. It takes a path and a number of threads. Rule of thumb: don't use all (virtual) cores on your computer, or instability may ensue. Note that this has a hard-coded log variable for the log file to write results for every test, by default `petr4_to_hol4p4_stf.log`.

`validate.sh` runs both `petr4_json_export.sh` and `petr4_to_hol4p4_dir.sh` targeted at `validation_tests`, and compiles the result with `Holmake` afterward. Note that this takes a number of parallel processes to use as an optional argument.

## HOL4 files

`excluded.sml` contains a list of tuples of categories (categorized by what blocks them from being parsed, as a string description) of tests and the test names themselves. Used to not waste time trying to re-transform tests you know will fail.

`parse_jsonScript.sml` is a theory of generic JSON objects.

`parse_stf.sml` parses an `.stf` specification of a test.

`petr4_to_hol4p4.sml` is the internal mechanism of `petr4_to_hol4p4_dir.sh` that does the actual format transformation from petr4 JSON to HOL4P4. `petr4_to_hol4p4Script.sml` holds the theorems needed for this, and `petr4_to_hol4p4Syntax.sml` the syntax library.

## Program transformations

In order to accommodate P4 programs in the syntax of HOL4P4, a bit of desugaring must be done.

### Nested programmable blocks

The most significant program transformation concerns inlining of nested blocks. Currently, only nested control blocks are supported and not nested parser blocks. This works in the following manner:

When instantiated blocks are applied (called), the apply block (body) of the nested block is inlined in the parent block, with all variables and tables prefixed with the instance name. The copy-in copy-out mechanism of block parameters is handled as follows:

Copy-in:
	* If the parameter is out, then the (prefixed) parameter is havoc-ed (by using arb_from_tau to assign a value with all bits as ARBs to it)
	* Otherwise, assign the argument to the (prefixed) parameter.
	
Copy-out:
	* If the parameter is out or inout, then assign the (prefixed) parameter to the L-value of the argument.
	* Otherwise, do nothing (note that this is safe since the import tool will halt with an error if prefixed variables of the inlined programmable block intersect with those of the parent block)
	
Actions (local functions) of inlined blocks must be able to access the block variables of their respective block. For this reason, all block variables of the nested block are added (prefixed) to the declaration list of the parent block (as opposed to being introduced inside a block) with their copy-out L-values set to NONE.

As an exception to the above, the local function maps `b_func_map` of the parent and child blocks are merged with no prefixing of action names, with the import tool halting with an error if name collisions are found for different entries.
	
After processing the entire program is complete, blocks which only occur as nested blocks will be removed from the pblock_map to avoid clutter.
	
Note that if the same block is instantiated twice, it uses different tables, while if it is instantiated once but applied twice, the same table is used.

This method cannot distinguish between tables of the same name in non-nested control blocks, nor between instances of the same name in separate programmable blocks. To avoid name collisions across nestings, all table names with dots are disallowed by the import tool.

Also, this method does not permit nested blocks from using a return statement to finish. Accordingly, the import tool halts with an error if inlining of programmable blocks with bodies containing return statements is attempted.

The new programmable block-variables resulting from the above procedure will be added to a "taboo list" - if these are encountered among the programmable block-variables of the parent block or in any variable declaration before the inlined block, the import tool will halt with an error.

### Select expressions

Select expressions with no default case will get a new default case that maps to the state "set_no_match", which contains only a "verify(false, error.NoMatch)" statement. The import tool will halt with an error if "set_no_match" is encountered among the regular states of the P4 program. The "set_no_match" state will only appear in programs with default-less select expressions.

## How to debug test files

Use `debug_arch_from_step`:
```
 val ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), ((i, in_out_list, in_out_list', ascope), g_scope_list, arch_frame_list, status)) = debug_arch_from_step "text_arch" test_name_actx test_name_astate nsteps
```
