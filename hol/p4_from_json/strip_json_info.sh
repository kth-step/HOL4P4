#!/bin/bash

perl -pi -e 's/\[\"info\",.*?\]/\[\"missing_info\",\"\"\]/g' $1
