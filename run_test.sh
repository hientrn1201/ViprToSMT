#!/bin/bash

# Check if the number of arguments is less than 1
if [ $# -lt 2 ]; then
    echo "Usage: $0 <block_size> <software>"
    exit 1
fi

# Define the list of file names
FILES=(
"30:70:4_5:0_95:100.vipr"
"acc-0.vipr"
"acc-1.vipr"
"acc-2.vipr"
"air03.vipr"
"air05.vipr"
"alu10_1.vipr"
"alu10_5.vipr"
"alu10_7.vipr"
"alu10_8.vipr"
"alu10_9.vipr"
"alu16_1.vipr"
"alu16_2.vipr"
"alu16_5.vipr"
"alu16_7.vipr"
"alu16_8.vipr"
"alu16_9.vipr"
"bc1.vipr"
"bell3a.vipr"
"bell5.vipr"
"bernd2.vipr"
"bienst1.vipr"
"bienst2.vipr"
"blend2.vipr"
"cnr_dual_mip1.vipr"
"cnr_heur_mip1.vipr"
"dano3_3.vipr"
"dano3_4.vipr"
"dano3_5.vipr"
"dcmulti.vipr"
"dfn6_load.vipr"
"dfn6f_cost.vipr"
"dfn6fp_cost.vipr"
"dfn6fp_load.vipr"
"egout.vipr"
"eilD76.vipr"
"enigma.vipr"
"flugpl.vipr"
"gen.vipr"
"gesa3.vipr"
"gesa3_o.vipr"
"ilp_sh5.vipr"
"ilp_sh6.vipr"
"irp.vipr"
"khb05250.vipr"
"l152lav.vipr"
"lseu.vipr"
"markshare1_1.vipr"
"markshare4_0.vipr"
"mas76.vipr"
"mas284.vipr"
"misc03.vipr"
"misc07.vipr"
"mod008.vipr"
"mod010.vipr"
"mod011.vipr"
"neos-522351.vipr"
"neos-619167.vipr"
"neos-799716.vipr"
"neos-839838.vipr"
"neos-1053591.vipr"
"neos-1062641.vipr"
"neos-1367061.vipr"
"neos-1603965.vipr"
"neos5.vipr"
"neos8.vipr"
"neos11.vipr"
"neos21.vipr"
"neos897005.vipr"
"neumaiershcherbina.vipr"
"normalized-aim-200-1_6-ye.vipr"
"normalized-aim-200-1_6-yes1-3.vipr"
"npmv07.vipr"
"ns1629327.vipr"
"ns1770598.vipr"
"ns1859355.vipr"
"ns1866531.vipr"
"ns1900685.vipr"
"ns1925218.vipr"
"ns2017839.vipr"
"ns2080781.vipr"
"nug08.vipr"
"opti_157_0.vipr"
"p0033.vipr"
"p0201.vipr"
"p4.vipr"
"pk1.vipr"
"prodplan1.vipr"
"prodplan2.vipr"
"qap10.vipr"
"qnet1_o.vipr"
"ran13x13.vipr"
"ran14x18.vipr"
"rentacar.vipr"
"rgn.vipr"
"sp98ir.vipr"
"stein27.vipr"
"stein45.vipr"
"swath1.vipr"
"swath2.vipr"
"tkat3K.vipr"
"tkat3T.vipr"
"tkat3TV.vipr"
"tkatTV5.vipr"
"vpm1.vipr"
"vpm2.vipr"
"x01.vipr"
)

# Get the value of -m from command line argument
BLOCK_SIZE="$1"
SOFTWARE="$2"

# Define the output CSV file name
OUTPUT_CSV="output.csv"


# Write CSV header
echo "File Name,Size,Valid,Time" > "$OUTPUT_CSV"

# Loop through each file name
for FILE in "${FILES[@]}"
do
    # Get file size
    FILE_SIZE=$(stat -c %s "tests/$FILE")
    
    # Run cargo command in background and capture the process ID
    cargo run -- -f "tests/$FILE" -m "$BLOCK_SIZE" -s "$SOFTWARE" > "temp_output.txt" 2>&1 &
    CARGO_PID=$!
    
    # Wait for the cargo command to finish
    wait "$CARGO_PID"
    
    # Read output from temporary file
    OUTPUT=$(< "temp_output.txt")

    echo "$OUTPUT"
    
    # Extract validity and time from the output
    VALID=$(echo "$OUTPUT" | grep -oE "tests\/.* is valid\.")
    TIME=$(echo "$OUTPUT" | grep -oE "Time elapsed: [0-9]*\.[0-9]*s")
    
    # Extract only the validity status
    VALIDITY=$(echo "$VALID" | cut -d' ' -f3)
    
    # Extract only the time
    TIME_VALUE=$(echo "$TIME" | cut -d' ' -f3)
    
    # Write to CSV file
    echo "$FILE,$FILE_SIZE,$VALIDITY,$TIME_VALUE" >> "$OUTPUT_CSV"
done

# Remove temporary file
rm "temp_output.txt"