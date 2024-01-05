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

## How to debug test files

Use `debug_arch_from_step`:
```
 val ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), ((i, in_out_list, in_out_list', ascope), g_scope_list, arch_frame_list, status)) = debug_arch_from_step "text_arch" test_name_actx test_name_astate nsteps
```
