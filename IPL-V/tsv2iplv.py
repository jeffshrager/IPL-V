# conda activate iplv
# python3 tsv2iplv.py LT_IPL-V-CODE_129-170.tsv LT_IPL-V-DATA_171-182.tsv LT_IPL-V-CODE_183-184.tsv LT_IPL-V-Exec_Code_71-73.tsv LT.iplv

# Line with a * in the "page" col are warned and suppressed -- this lets us surgically remove lines.

import pandas as pd
import argparse

# Set up argument parser
parser = argparse.ArgumentParser(description="Convert TSV files to IPL-V input cards")
parser.add_argument("input_files", nargs='+', help="List of input TSV files")
parser.add_argument("output_file", help="Output file for formatted IPL-V cards")
args = parser.parse_args()

# Function to clean and format data
def format_iplv_line(row, line_num):
    try:
        page = row.get("Page", "")
        comment = row.get("Comments", "").replace("_", "").ljust(35)[:35]
        type_field = row.get("Type", "").strip().ljust(1)[:1]
        name = row.get("Name", "").replace("_", "").ljust(5)[:5]
        sign = row.get("Sign", "").strip().ljust(1)[:1]
        pq = row.get("PQ", "").strip().zfill(2)[:2]  # Ensure two-digit format
        symb = row.get("Symb", "").strip().ljust(5)[:5]
        link = row.get("Link", "").strip().ljust(5)[:5]
        comments = row.get("Comments.1", "").replace("_", "").ljust(10)[:10]
        id_field = row.get("ID", "").strip().replace(" ", "").ljust(8)[:8]  # Preserve leading zeros
        
        # Formatting according to the specified column structure
        formatted_line = f"{'':5}{comment}{type_field}{'':1}{name}{sign}{pq}{symb}{'':1}{link}{'':1}{comments}{id_field}"
        if page.find('*') > 0:
            print(page)
            print("Line suppressed:\n"+formatted_line+"\n")
            return None
        else:
            return formatted_line
    except Exception as e:
        print(f"Error processing line {line_num}: {e}")
        print(formatted_line)
        return None

# Process each input file
formatted_lines = []
for file_path in args.input_files:
    print(f"Opening file: {file_path}")
    df = pd.read_csv(file_path, sep="	", dtype=str, keep_default_na=False)
    df = df.astype(str).map(lambda x: x.replace('_', ''))  # Ensure all columns are treated as strings
    for line_num, (_, row) in enumerate(df.iterrows(), start=1):
        if line_num % 100 == 0:
            print(f"Processing line {line_num}...")
        formatted_line = format_iplv_line(row, line_num)
        if formatted_line:
            formatted_lines.append(formatted_line)

# Save to output file
with open(args.output_file, "w") as f:
    for line in formatted_lines:
        f.write(line + "\n")

print(f"Formatted IPL-V input cards saved to {args.output_file}")
