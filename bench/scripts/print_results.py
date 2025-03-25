#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import os

try:
    import pandas as pd
except ImportError:
    sys.stderr.write("pandas must be installed\n")
    sys.exit(1)

"""
How to call the script:

./print_results.py (prints a table to stdout reading the results from "results.txt")
./print_results.py <file> (prints a table to stdout reading the results from <file>)

./print_results.py -tex (prints a latex table to stdout reading the results from "results.txt")
./print_results.py -tex <file> (prints a latex table to stdout reading the results from <file>)

The file with the benchmark results is expected to have the following format:

Function;Average;Median ==> These must be the headers
prf_jasmin;3113;2853    ==> Benchmarks of jasmin functions must have the "_jasmin" suffix
prf_ref;4226;3003       ==> Benchmarks of functions from the C reference impl must have the "_ref" suffix
"""


def parse_args() -> tuple[bool, str]:
    # default
    print_tex = False
    filepath = "results.txt"

    if len(sys.argv) > 1:
        if sys.argv[1] == "-tex":
            print_tex = True
            if len(sys.argv) > 2:
                if os.path.exists(sys.argv[-1]):
                    filepath = sys.argv[-1]
        else:
            filepath = sys.argv[-1]

    if not os.path.exists(filepath):
        sys.stderr.write(f"The file '{filepath}' does not exist\n")
        sys.exit(1)

    return print_tex, filepath


def read_data(filepath: str) -> pd.DataFrame:
    assert os.path.exists(filepath)  # this was already checked when parsing the arguments

    try:
        data = pd.read_csv(filepath, sep=";")
    except Exception as e:
        sys.stderr.write(f"Error reading the file to csv: {e}\n")

    data.columns = ["Function", "Average", "Median"]
    data["Basename"] = data["Function"].str.replace(r"_(ref|jasmin)$", "", regex=True)

    grouped = data.groupby("Basename")

    try:
        result = pd.DataFrame()

        for basename, group in grouped:
            row = {"Basename": basename}
            for _, entry in group.iterrows():
                if "_ref" in entry["Function"]:
                    row["Average Ref"] = entry["Average"]
                    row["Median Ref"] = entry["Median"]
                elif "_jasmin" in entry["Function"]:
                    row["Average Jasmin"] = entry["Average"]
                    row["Median Jasmin"] = entry["Median"]
            result = pd.concat([result, pd.DataFrame([row])], ignore_index=True)

            result["Faster Implementation"] = result.apply(
                lambda row: "Jasmin" if row["Median Jasmin"] < row["Median Ref"] else "Ref", axis=1
            )

            result["Diff (%)"] = result.apply(
                lambda row: round(
                    abs((row["Median Ref"] - row["Median Jasmin"]) / row["Median Ref"]) * 100, 2
                ),
                axis=1,
            )

        result.rename(columns={"Basename": "Function"}, inplace=True)
    except Exception:
        sys.stderr.write("Failed\n")
        sys.stderr.write(
            "Make sure the jasmin function end with the _jasmin suffix and the C functions end with the _ref suffix \n"
        )
        sys.exit(1)

    return result


def print_latex_table(table: pd.DataFrame):
    """
    Obs: this requires the package \ usepackage{booktabs}
    """

    assert table is not None

    print(r"\begin{table}[H]")
    print(r"    \centering")
    print(r"    \begin{tabular}{l c c c c}")
    print(r"        \toprule")
    print(r"        Function & Average Ref & Median Ref & Average Jasmin & Median Jasmin \\")
    print(r"        \midrule")

    for _, row in table.iterrows():
        foo = row["Function"].replace("_", "\_")
        fn_name = f"\\texttt{{{foo}}}"
        print(
            f"        {fn_name} & {row['Average Ref']} & {row['Median Ref']} & {row['Average Jasmin']} & {row['Median Jasmin']} \\\\"
        )

    print(r"        \bottomrule")
    print(r"    \end{tabular}")
    print(r"    \caption{Benchmark results comparing Ref and Jasmin implementations}")
    print(r"\end{table}")


def main():
    print_tex, input_filepath = parse_args()
    table = read_data(input_filepath)

    if "-noavg" in sys.argv:
        table = table.drop(columns=[col for col in table.columns if "Average" in col])

    if print_tex:
        print_latex_table(table.drop(columns=["Faster Implementation"]))
    else:
        print(table.to_string(index=False))

    return 0


if __name__ == "__main__":
    sys.exit(main())
