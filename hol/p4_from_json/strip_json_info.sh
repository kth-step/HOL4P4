#!/bin/bash
#This script is used to remove content of debugging fields from petr4 .json output

perl -pi -e 's/\[\"info\",.*?\]/\[\"missing_info\",\"\"\]/g' $1
