#!/bin/bash

touch output.txt

lFiles=("Blood"
        "BloodInventory"
        "Filtering"
        #"MergeSort"
        "QueryBloodInventory"
        "Request"
        "Searching"
        "SortBloodInventory"
        "Test")

errors=0; time=0;
echo "checking all Dafny files"
for i in "${!lFiles[@]}"
do
    echo "----------------------------------------------------------------" >> output.txt
    printf "%s \e[1;33m%-19s\e[0m " "($((i+1))/${#lFiles[@]})" "${lFiles[i]}"
    echo "running ${lFiles[i]}.dfy" >> output.txt
    echo "" >> output.txt
    t=$({ TIMEFORMAT="%1U"; time dafny /compile:3 ${lFiles[i]}.dfy >> output.txt; } 2>&1)
    if [ $? -eq 0 ]; then
        printf -- "- \e[1;32mpassed\e[0m (${t}s)\n"
    else
        printf -- "- \e[1;31merrors\e[0m\n"; ((errors++))
    fi
    echo "" >> output.txt
    time=$(echo "$time+$t" | bc)
done
echo "finished in ${time}s"
if [ $errors -eq 0 ]; then
    printf "all checks passed - You are awesome!\n"
else
    echo "verified all files with $((${#lFiles[@]}-$errors)) passed, ${errors} errors"
fi
