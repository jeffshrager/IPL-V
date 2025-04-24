# conda activate iplv
# python3 tsv2lisp.py LT_IPL-V-CODE_129-170.tsv LT_IPL-V-DATA_171-182.tsv LT_IPL-V-CODE_183-184.tsv LT_IPL-V-Exec_Code_71-73.tsv LT.liplv
# python3 tsv2lisp.py F1.tsv F1.liplv

# WWW FFF Need to also delete double quotes (") [Although I think that
# through magical thinking, these worked correctly -- see, e.g.,
# K1-K7)

# WWW FFF Note that this creates multiple column headers (one per
# file) that need to be hand-edited out. Easy to fix.

import pandas as pd
import argparse

# Set up argument parser
parser = argparse.ArgumentParser(description="Convert TSV files to a Lisp alist")
parser.add_argument("input_files", nargs='+', help="List of input TSV files")
parser.add_argument("output_file", help="Output file for the Lisp alist")
args = parser.parse_args()

# Relevant columns for the output
relevant_columns = ["Comments", "Type", "Name", "Sign", "PQ", "Symb", "Link", "Comments.1", "ID"]

# Process each input file
lisp_data = []
for file_path in args.input_files:
    print(f"Opening file: {file_path}")
    df = pd.read_csv(file_path, sep="\t", dtype=str, keep_default_na=False)
    df = df.astype(str).map(lambda x: (x.replace('_', '')).replace('\"', ''))  # Ensure strings and remove underbars and double quotes
    
    # Create header row with field names
    header_expr = "(" + " ".join(f":{col.lower().replace(' ', '_')}" for col in relevant_columns) + ")"
    
    # Create data rows
    file_lisp_data = ["(" + " ".join(f'"{row[col]}"' for col in relevant_columns) + ")" 
                       for _, row in df.iterrows() if '*' not in row.get("Page", "")]
    
    lisp_data.append(header_expr)
    lisp_data.extend(file_lisp_data)

# Format as an s-expression with newlines
lisp_output = "(\n" + "\n".join(lisp_data) + "\n)"

# Save to output file
with open(args.output_file, "w") as f:
    f.write(lisp_output + "\n")

print(f"Lisp alist saved to {args.output_file}")
