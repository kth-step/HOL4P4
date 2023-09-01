#Shell scripts

`petr4_json_export.sh` uses petr4 to transform .p4 programs to JSON. It takes a path as a command line argument and will transform all .p4 programs found there to .json files. Note that this involves a hard-coded "P4_INCLUDE" variable that should point to .p4 files contain architecture descriptions.

`strip_json_info.sh` takes a file name as a command-line argument and tries to remove debug information from the JSON in the file.

`petr4_to_hol4p4_dir.sh` takes a path as a command-line argument and tries to transform all .json files found there into HOL4P4 .sml files (using `petr4_to_hol4p4.sh`). Note that this has the following hard-coded variables:
* N: The number of processes to use. Rule of thumb: don't use all (virtual) cores on your computer, or instability may ensue.
* log: The log file to write results for every test
* remove_debug: This flag decides whether the `strip_json_info.sh` script will be used on all .json files involved, removing very verbose debug information, shrinking the size of the .json considerably.

#HOL4 files

`excluded.sml` contains a list of tuples of categories (categorized by what blocks them from being parsed, as a string description) of tests and the test names themselves. Used to not re-transform tests you know will fail.

`parse_vss_test.sml` is intended to demonstrate that the HOL4P4 terms obtained from petr4 match the hand-written ones.

`parse_jsonScript.sml` is a theory of generic JSON objects.

`parse_stf.sml` parses an `.stf` specification of a test.

`petr4_to_hol4p4.sml` is the internal mechanism of `petr4_to_hol4p4_dir.sh` that does the actual format transformation from petr4 JSON to HOL4P4. `petr4_to_hol4p4Script.sml` holds the theorems needed for this, and `petr4_to_hol4p4Syntax.sml` the syntax library.

#How to debug test files

Use `debug_arch_from_step`:
```
 val ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), ((i, in_out_list, in_out_list', ascope), g_scope_list, arch_frame_list, status)) = debug_arch_from_step "text_arch" test_name_actx test_name_astate nsteps
```
