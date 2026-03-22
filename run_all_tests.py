#!/usr/bin/env python3
"""
Ontodynamique — Full Validation Pipeline Runner
================================================

Reproduces every figure and statistic from the manuscript.
Designed to run inside Docker (all dependencies pre-installed)
or standalone on any machine with the correct environment.

Usage:
  python run_all_tests.py                  # Run everything
  python run_all_tests.py --section lean   # Run only Lean verification
  python run_all_tests.py --section mdsine2 gdsc corail  # Run specific sections
  python run_all_tests.py --list           # List available sections

Sections:
  lean        — Compile & verify all Lean 4 formalization files
  mdsine2     — Microbiome analysis (phases 1–4 + rival partitions)
  gdsc        — Cancer pharmacology (GDSC1, GDSC2, rival partitions)
  corail      — Coral reef analysis + temporal split
  yeast_hom   — Yeast phenome homozygous (exploratory)
  yeast_het   — Yeast phenome heterozygous (confirmatory, OSF)
  crossdomain — Cross-domain specificity & sensitivity checks
  meta        — Meta-analysis figures
  artificial  — Artificial life simulation (R-XIX)
"""

import argparse
import glob
import os
import re
import subprocess
import sys
import time
from pathlib import Path

# ── Configuration ────────────────────────────────────────────────────────────

BASE_DIR = Path(__file__).resolve().parent
OUTPUT_DIR = BASE_DIR / "output"
OUTPUT_DIR.mkdir(exist_ok=True)

# Color codes for terminal output
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
CYAN = "\033[96m"
BOLD = "\033[1m"
RESET = "\033[0m"


# ── Section definitions ──────────────────────────────────────────────────────

SECTIONS = {
    "lean": {
        "name": "Lean 4 Formalization",
        "description": "Compile & verify all Lean files (0 sorry)",
        "runner": "_run_lean",
    },
    "mdsine2": {
        "name": "MDSINE2 Microbiome",
        "description": "Phases 1–4 + rival partitions",
        "scripts": [
            "ScriptMDSINE2/01_phase1_raw_metrics.py",
            "ScriptMDSINE2/02_phase2_corrected.py",
            "ScriptMDSINE2/03_phase3_interaction_matrix.py",
            "ScriptMDSINE2/04_robustness_metrics.py",
            "ScriptMDSINE2/05_rival_partitions_mdsine2.py",
        ],
    },
    "gdsc": {
        "name": "Cancer Pharmacology (GDSC)",
        "description": "GDSC1, GDSC2, cell-line split, rival partitions",
        "scripts": [
            "ScriptGDSC/GDSC1.py",
            "ScriptGDSC/GDSC2.py",
            "ScriptGDSC/gdsc_cellline_split.py",
            "ScriptGDSC/rXVII_rival_partitions.py",
        ],
    },
    "corail": {
        "name": "Coral Reef Analysis",
        "description": "Reef bleaching + temporal split CR-02A",
        "scripts": [
            "ScriptCorail/corail.py",
            "ScriptCorail/reef_temporal_split.py",
            "ScriptCorail/rival_partitions_reef.py",
            "ScriptCorail/robustness_reef.py",
        ],
    },
    "yeast_hom": {
        "name": "Yeast Phenome — Homozygous (exploratory)",
        "description": "R-XVII hom + rival partitions + robustness",
        "scripts": [
            ("ScriptYeast/RXVII.py", [
                "--matrix", "yp_matrix_z_haphom_20221025.txt",
                "--screens", "yp_screens_haphom_20221025.txt",
                "--gaf", "gene_association.sgd.20251124.gaf",
            ]),
            ("ScriptYeast/rival_partitions_yeast.py", [
                "--matrix", "yp_matrix_z_haphom_20221025.txt",
                "--screens", "yp_screens_haphom_20221025.txt",
                "--gaf", "gene_association.sgd.20251124.gaf",
            ]),
            ("ScriptYeast/robustness_yeast.py", [
                "--matrix", "yp_matrix_z_haphom_20221025.txt",
                "--screens", "yp_screens_haphom_20221025.txt",
                "--gaf", "gene_association.sgd.20251124.gaf",
            ]),
        ],
    },
    "yeast_het": {
        "name": "Yeast Phenome — Heterozygous (confirmatory)",
        "description": "R-XVII het + robustness (pre-registered OSF)",
        "scripts": [
            ("ScriptYeast/RXVII.py", [
                "--matrix", "yp_matrix_het_z_20221018.txt",
                "--screens", "yp_screens_het_20221018.txt",
                "--gaf", "gene_association.sgd.20251124.gaf",
            ]),
            ("ScriptYeast/robustness_yeast.py", [
                "--matrix", "yp_matrix_het_z_20221018.txt",
                "--screens", "yp_screens_het_20221018.txt",
                "--gaf", "gene_association.sgd.20251124.gaf",
            ]),
        ],
    },
    "crossdomain": {
        "name": "Cross-Domain Specificity",
        "description": "Specificity + sensitivity checks",
        "scripts": [
            "ScriptCrossDomain/crossDomainCheck.py",
            "ScriptCrossDomain/SpecifityCheck.py",
            "ScriptCrossDomain/Sentsivity.py",
        ],
    },
    "meta": {
        "name": "Meta-Analysis Figures",
        "description": "Forest plot + gradient figures",
        "scripts": [
            ("ScriptMetaAnalyse/preprint_figures.py", [
                "--all",
                "--reef-csv", "../ScriptCorail/global_bleaching_environmental.csv",
                "--gdsc-csv", "../ScriptGDSC/sanger-dose-response.csv",
                "--yeast-matrix", "../ScriptYeast/yp_matrix_z_haphom_20221025.txt",
                "--yeast-screens", "../ScriptYeast/yp_screens_haphom_20221025.txt",
                "--yeast-gaf", "../ScriptYeast/gene_association.sgd.20251124.gaf",
                "--yeast-het-matrix", "../ScriptYeast/yp_matrix_het_z_20221018.txt",
                "--yeast-het-screens", "../ScriptYeast/yp_screens_het_20221018.txt",
                "--mdsine2-paper", "../MDSINE2_Paper",
            ]),
        ],
    },
    "artificial": {
        "name": "Artificial Life (R-XIX)",
        "description": "Simulated self-maintaining systems",
        "scripts": [
            "ScriptArtificialLife/al.py",
        ],
    },
}


# ── Lean runner ──────────────────────────────────────────────────────────────

def _run_lean():
    """Compile all .lean files and check for 0 sorry."""
    lean_dir = BASE_DIR / "Lean"
    lean_files = sorted(lean_dir.glob("*.lean"))

    if not lean_files:
        print(f"  {RED}No .lean files found in {lean_dir}{RESET}")
        return False

    print(f"  Found {len(lean_files)} Lean files to verify.\n")
    all_ok = True

    for lf in lean_files:
        print(f"  Compiling {lf.name}...", flush=True)
        t0 = time.time()
        result = subprocess.run(
            ["lean", str(lf)],
            timeout=900
        )
        elapsed = time.time() - t0

        if result.returncode == 0:
            # Check for sorry tactic (skip comments and strings)
            content = lf.read_text()
            # Remove single-line comments
            no_comments = re.sub(r'--.*', '', content)
            # Remove block comments /- ... -/
            no_comments = re.sub(r'/-.*?-/', '', no_comments, flags=re.DOTALL)
            # Remove string literals
            no_strings = re.sub(r'"[^"]*"', '', no_comments)
            # Count standalone sorry keyword (not part of another word)
            sorry_count = len(re.findall(r'\bsorry\b', no_strings))
            if sorry_count > 0:
                print(f"  {YELLOW}OK but {sorry_count} sorry found{RESET} ({elapsed:.1f}s)")
                all_ok = False
            else:
                print(f"  {GREEN}OK{RESET} ({elapsed:.1f}s)")
        else:
            print(f"  {RED}FAILED{RESET} ({elapsed:.1f}s)")
            all_ok = False

    return all_ok


# ── Python script runner ─────────────────────────────────────────────────────

def run_python_script(script_entry) -> bool:
    """Run a single Python script with proper working directory.

    script_entry can be:
      - a string: "ScriptGDSC/GDSC1.py"
      - a tuple:  ("ScriptYeast/RXVII.py", ["--matrix", "file.txt", ...])
    """
    if isinstance(script_entry, tuple):
        script_path, extra_args = script_entry
    else:
        script_path, extra_args = script_entry, []

    full_path = BASE_DIR / script_path
    script_dir = full_path.parent

    if not full_path.exists():
        print(f"  {RED}Script not found: {script_path}{RESET}")
        return False

    print(f"  Running {script_path}...", flush=True)
    t0 = time.time()

    try:
        result = subprocess.run(
            [sys.executable, "-u", str(full_path)] + extra_args,
            cwd=str(script_dir),
            timeout=1800,  # 30 min max per script
            env={**os.environ, "MPLBACKEND": "Agg", "PYTHONUNBUFFERED": "1"},
        )
        elapsed = time.time() - t0

        if result.returncode == 0:
            print(f"  {GREEN}✓ {script_path}{RESET} ({elapsed:.1f}s)")
            return True
        else:
            print(f"  {RED}✗ {script_path}{RESET} ({elapsed:.1f}s)")
            return False

    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        print(f"  {RED}✗ {script_path} TIMEOUT{RESET} ({elapsed:.1f}s)")
        return False


# ── Section runner ───────────────────────────────────────────────────────────

def run_section(key: str) -> dict:
    """Run a full section, return results dict."""
    section = SECTIONS[key]
    print(f"\n{'='*70}")
    print(f"{BOLD}{CYAN}  {section['name']}{RESET}")
    print(f"  {section['description']}")
    print(f"{'='*70}\n")

    t0 = time.time()

    if "runner" in section:
        # Custom runner (e.g., Lean)
        runner_fn = globals()[section["runner"]]
        success = runner_fn()
        results = {
            "section": key,
            "name": section["name"],
            "total": 1,
            "passed": 1 if success else 0,
            "failed": 0 if success else 1,
            "elapsed": time.time() - t0,
        }
    else:
        # Python scripts
        scripts = section.get("scripts", [])
        passed = 0
        failed = 0
        for script in scripts:
            ok = run_python_script(script)
            if ok:
                passed += 1
            else:
                failed += 1

        results = {
            "section": key,
            "name": section["name"],
            "total": len(scripts),
            "passed": passed,
            "failed": failed,
            "elapsed": time.time() - t0,
        }

    return results


# ── Summary ──────────────────────────────────────────────────────────────────

def print_summary(all_results: list):
    """Print a final summary table."""
    print(f"\n{'='*70}")
    print(f"{BOLD}  SUMMARY{RESET}")
    print(f"{'='*70}")
    print(f"  {'Section':<30} {'Passed':>8} {'Failed':>8} {'Time':>10}")
    print(f"  {'-'*56}")

    total_passed = 0
    total_failed = 0
    total_time = 0

    for r in all_results:
        status_color = GREEN if r["failed"] == 0 else RED
        print(
            f"  {r['name']:<30} "
            f"{GREEN}{r['passed']:>8}{RESET} "
            f"{status_color}{r['failed']:>8}{RESET} "
            f"{r['elapsed']:>9.1f}s"
        )
        total_passed += r["passed"]
        total_failed += r["failed"]
        total_time += r["elapsed"]

    print(f"  {'-'*56}")
    overall_color = GREEN if total_failed == 0 else RED
    print(
        f"  {'TOTAL':<30} "
        f"{GREEN}{total_passed:>8}{RESET} "
        f"{overall_color}{total_failed:>8}{RESET} "
        f"{total_time:>9.1f}s"
    )
    print()

    if total_failed == 0:
        print(f"  {GREEN}{BOLD}All tests passed!{RESET}")
    else:
        print(f"  {RED}{BOLD}{total_failed} test(s) failed.{RESET}")

    return total_failed == 0


# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Ontodynamique — Full Validation Pipeline"
    )
    parser.add_argument(
        "--section", "-s",
        nargs="+",
        choices=list(SECTIONS.keys()),
        help="Run only specific sections",
    )
    parser.add_argument(
        "--list", "-l",
        action="store_true",
        help="List available sections and exit",
    )
    parser.add_argument(
        "--skip-lean",
        action="store_true",
        help="Skip Lean verification (faster for Python-only testing)",
    )
    args = parser.parse_args()

    if args.list:
        print("\nAvailable sections:")
        for key, sec in SECTIONS.items():
            print(f"  {key:<15} {sec['name']} — {sec['description']}")
        sys.exit(0)

    # Determine which sections to run
    if args.section:
        sections_to_run = args.section
    else:
        sections_to_run = list(SECTIONS.keys())

    if args.skip_lean and "lean" in sections_to_run:
        sections_to_run.remove("lean")

    print(f"\n{BOLD}Ontodynamique — Validation Pipeline{RESET}")
    print(f"Sections: {', '.join(sections_to_run)}")
    print(f"Output:   {OUTPUT_DIR}")

    # Run all sections
    all_results = []
    for key in sections_to_run:
        results = run_section(key)
        all_results.append(results)

    # Summary
    all_ok = print_summary(all_results)
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
