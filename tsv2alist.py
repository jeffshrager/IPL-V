# conda activate iplv
# python3 tsv2alist.py LT_IPL-V-CODE_129-170.tsv LT_IPL-V-DATA_171-182.tsv LT_IPL-V-CODE_183-184.tsv LT_IPL-V-Exec_Code_71-73.tsv LT.lisp

import pandas as pd
import argparse

# Set up argument parser
parser = argparse.ArgumentParser(description="Convert TSV files to a Lisp alist")
parser.add_argument("input_files", nargs='+', help="List of input TSV files")
parser.add_argument("output_file", help="Output file for the Lisp alist")
args = parser.parse_args()

# Relevant columns for the output
relevant_columns = {"Comments", "Type", "Name", "Sign", "PQ", "Symb", "Link", "Comments.1", "ID"}

# Function to convert a row to a Lisp-style alist
def row_to_lisp_alist(row):
    if '*' in row.get("Page", ""):  # Suppress rows where Page contains '*'
        print("Suppressed " + str(row) + "\n")
        return None
    return "(" + " ".join(f":{col.lower().replace(' ', '_')} \"{row[col]}\"" for col in row.index if col in relevant_columns) + ")"

# Process each input file
lisp_data = []
for file_path in args.input_files:
    print(f"Opening file: {file_path}")
    df = pd.read_csv(file_path, sep="\t", dtype=str, keep_default_na=False)
    df = df.astype(str).map(lambda x: x.replace('_', ''))  # Ensure strings and remove underbars
    
    file_lisp_data = [row_to_lisp_alist(row) for _, row in df.iterrows()]
    file_lisp_data = [entry for entry in file_lisp_data if entry]  # Remove suppressed rows
    lisp_data.extend(file_lisp_data)

# Format as an s-expression with newlines
lisp_output = "(\n" + "\n".join(lisp_data) + "\n)"

# Save to output file
with open(args.output_file, "w") as f:
    f.write(lisp_output + "\n")

print(f"Lisp alist saved to {args.output_file}")
