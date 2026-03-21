# GDSC Data — Download Instructions

## 1. Drug response data: `sanger-dose-response.csv`

The GDSC drug sensitivity data has moved to the **Sanger DepMap / Cell Model Passports**.

1. Go to **https://cellmodelpassports.sanger.ac.uk/downloads**
2. Scroll to **Functional Datasets**
3. Download **"GDSC1 IC50 Data (Legacy Dataset)"** or **"GDSC2 IC50 Data"**
4. The downloaded file contains IC50, AUC, and Z-Score values

The file used in our scripts is `sanger-dose-response.csv` which combines GDSC1 and GDSC2.
If you download them separately, either one works — the scripts auto-detect the columns.

## 2. Cell line annotations: `model_list_*.csv`

Required for the rival partition test (cancer type stratification).

1. Go to **https://cellmodelpassports.sanger.ac.uk/downloads**
2. First item: **"Model List"** — "Download list of all annotated models"
3. The file downloads as `model_list_YYYYMMDD.csv`
4. Place it in the same folder as the scripts — it is auto-detected by name pattern

Key columns used: `COSMIC_ID`, `cancer_type`, `tissue`.

## 3. File locations

```
ScriptGDSC/
├── sanger-dose-response.csv          # drug response (step 1)
├── model_list_20260316.csv           # cell line annotations (step 2)
├── rXVII_rival_partitions.py         # rival partition test
├── GDSC1.py                          # R-XVII v1
├── GDSC2.py                          # R-XVII v2 (pathway-only)
└── gdsc_cellline_split.py            # CR-02B cross-validation
```
