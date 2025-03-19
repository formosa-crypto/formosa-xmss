#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import os

try:
    import pandas as pd
except ImportError:
    sys.stderr.write("pandas must be installed\n")
    sys.exit(1)

if len(sys.argv) > 1:
    file_path = sys.argv[1]
else:
    file_path = "results.txt"

if not os.path.exists(file_path):
    sys.stderr.write(f"The file '{file_path}' does not exist\n")
    sys.exit(1)

try:
    data = pd.read_csv(file_path, sep=";")
except Exception as e:
    sys.stderr.write(f"Error reading the file to csv: {e}\n")

data.columns = ["Function", "Average", "Median"]


data["Basename"] = data["Function"].str.replace(r"_(ref|jasmin)$", "", regex=True)

# print(data)

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

    result.rename(columns={"Basename": "Function"}, inplace=True)
    print(result.to_string(index=False))
except Exception:
    sys.stderr.write("ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZzz\n")
    sys.exit(1)
    