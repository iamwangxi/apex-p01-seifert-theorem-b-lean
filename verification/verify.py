#!/usr/bin/env python3
# Copyright (c) 2026 Topo contributors.
# Released under the Apache 2.0 license; see LICENSE.
"""Offline acceptance using Python's standard library and the pinned Lake/Lean tools.

No repository history or dependency-management commands are queried. Install the
locked dependencies before running this script. Generated logs use relative paths.
"""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "verification/results"
FROZEN = {
    "Statements.lean": "edc0bc63091ff229803fba68a31ea02db58ac675697b19caede0d3725e78d699",
    "ApplicationStatements.lean": "9da62de1dedac115f38b0d26d669ca2082f042ab00c5ef84d7184f3c6786998a",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ALLOWED_OPTIONS = {
    ("Topo/ExchangeSeven.lean", "maxRecDepth", "4096"),
    ("Topo/ExchangeSeven.lean", "maxHeartbeats", "1000000"),
}
FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|implemented_by|unsafe|opaque|extern)\b"
)
PRIVATE_DIRS = {".git", ".lake", ".agents", ".codex", ".aws", "__pycache__"}
MAIN_THEOREMS = {
    "SeifertAudit.theoremB_verified",
    "SeifertApplicationAudit.theoremA_verified",
    "SeifertApplicationAudit.theoremC_genus_verified",
    "SeifertApplicationAudit.theoremC_area_verified",
    "SeifertApplicationStatement.areaValues_finite_Iic",
    "SeifertApplicationStatement.areaValues_isClosed",
    "SeifertApplicationStatement.areaValues_discreteTopology",
    "SeifertApplicationStatement.areaValues_closed_discrete_positive",
    "SeifertApplicationStatement.areaValues_orderEmbedding",
    "SeifertApplicationStatement.values_orderEmbedding",
    "SeifertApplicationStatement.values_wellFounded",
    "SeifertApplicationStatement.vertices_countable",
    "SeifertApplicationStatement.theoremA_of_finiteFibres",
    "SeifertApplicationStatement.theoremC_genus_of_finiteFibres",
    "SeifertApplicationStatement.theoremC_area_of_finiteFibres",
    "SeifertApplicationStatement.theoremD_of_finiteFibres",
    "Seifert.Application.theoremD",
    "Seifert.theoremB",
    "AdversarialAudit.two_isolated_not_contractible",
    "AdversarialAudit.empty_not_contractible",
    "AdversarialAudit.edgeHomeomorphUnitInterval",
    "AdversarialAudit.lower_six_not_cone",
    "Seifert.Application.DisconnectedTwo.not_contractible",
}
LIBRARY_ROOTS = ["Topo", "Statements", "ApplicationStatements",
                 "verification.Axioms", "verification.Types"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def scrub(text):
    text = text.replace(str(ROOT), ".")
    text = re.sub(r"/(?:Users|home)/[^\s\"'<>`)\],;:]+", "[local-path]", text)
    return re.sub(r"/(?:private/)?(?:tmp|var/folders)/[^\s\"'<>`)\],;:]+",
                  "[temporary-path]", text)


def public_files():
    """Do not enter dependencies, repository metadata or private configuration."""
    result = []
    for base, dirs, files in os.walk(ROOT, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in PRIVATE_DIRS)
        for directory in dirs:
            path = Path(base) / directory
            if path.is_symlink():
                raise RuntimeError("Public directory is a symlink: " + str(path.relative_to(ROOT)))
        for name in sorted(files):
            if name.startswith(".env") or name.endswith((".pem", ".key")):
                continue
            path = Path(base) / name
            if path.is_symlink():
                raise RuntimeError("Public file is a symlink: " + str(path.relative_to(ROOT)))
            result.append(path)
    return sorted(result)


def code_only(text):
    """Blank nested comments and strings without moving any line or character."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
                continue
            if text[i] == '"':
                string = False
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
            continue
        if text[i] == '"':
            out[i] = " "
            string = True
        i += 1
    if depth or string:
        raise RuntimeError("Unterminated Lean comment or string")
    return "".join(out)


def source_scan(paths):
    hits, options = [], []
    for path in paths:
        rel = path.relative_to(ROOT).as_posix()
        code = code_only(path.read_text())
        for match in FORBIDDEN.finditer(code):
            hits.append({"path": rel, "line": code[:match.start()].count("\n") + 1,
                         "token": match.group()})
        for match in re.finditer(r"\bset_option\s+(\S+)\s+(\S+)", code):
            option, value = match.groups()
            allowed = (rel, option, value) in ALLOWED_OPTIONS
            options.append({"path": rel, "line": code[:match.start()].count("\n") + 1,
                            "option": option, "value": value, "allowed": allowed})
        # A malformed command must not slip past the option parser.
        if len(re.findall(r"\bset_option\b", code)) != sum(r["path"] == rel for r in options):
            hits.append({"path": rel, "token": "unparsed set_option"})
    report = {"lean_files": len(paths), "forbidden_hits": hits, "set_options": options,
              "scope": "All repository Lean files; dependency and private metadata trees excluded"}
    write_json("source-scan.json", report)
    if hits or any(not r["allowed"] for r in options):
        raise RuntimeError("Source scan failed; see source-scan.json")
    for option in options:
        print("Allowed option: {path}:{line}: {option} {value}".format(**option), flush=True)
    return report


def frozen_check():
    records = [{"path": name, "expected": digest, "actual": sha(ROOT / name)}
               for name, digest in FROZEN.items()]
    for record in records:
        record["ok"] = record["expected"] == record["actual"]
    write_json("frozen-statements.json", records)
    if not all(r["ok"] for r in records):
        raise RuntimeError("Frozen statement changed")
    for name in FROZEN:
        imports = re.findall(r"^import\s+(\S+)\s*$", code_only((ROOT / name).read_text()), re.M)
        if imports != ["Mathlib"]:
            raise RuntimeError("Statement is no longer Mathlib-only: " + name)
    return records


def build_coverage(paths):
    modules = {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): p
               for p in paths}
    edges = {}
    for module, path in modules.items():
        code = code_only(path.read_text())
        edges[module] = [name for line in re.findall(r"^import\s+([^\n]+)$", code, re.M)
                         for name in line.split() if name in modules]
    # These are the default target and roots declared in the release configuration.
    config = (ROOT / "lakefile.toml").read_text()
    if not re.search(r'defaultTargets\s*=\s*\["Topo"\]', config):
        raise RuntimeError("Default target changed")
    roots_match = re.search(r'^roots\s*=\s*\[([^]]+)\]', config, re.M)
    if not roots_match or re.findall(r'"([^"]+)"', roots_match[1]) != LIBRARY_ROOTS:
        raise RuntimeError("Library roots changed")
    reached, pending = set(), list(LIBRARY_ROOTS)
    while pending:
        module = pending.pop()
        if module not in modules:
            raise RuntimeError("Missing library root: " + module)
        if module not in reached:
            reached.add(module)
            pending.extend(edges[module])
    missing = sorted(set(modules) - reached)
    report = {"default_target": "Topo", "default_build_modules": len(modules),
              "project_modules": sum(not m.startswith("verification.") for m in modules),
              "covered_modules": sorted(reached), "uncovered_modules": missing,
              "verification_harnesses": sorted(p.relative_to(ROOT).as_posix() for p in paths
                                                if "verification" in p.relative_to(ROOT).parts)}
    write_json("build-coverage.json", report)
    if missing:
        raise RuntimeError("Default build omits modules: " + ", ".join(missing))
    return report


def dependency_preflight():
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0-rc3":
        raise RuntimeError("Unexpected Lean toolchain")
    lock = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = [p for p in lock["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != "c55e6e786f49471c72fbddbec5415808896aec1e":
        raise RuntimeError("Unexpected Mathlib lock revision")
    for package in lock["packages"]:
        if not (ROOT / ".lake/packages" / package["name"] / package["configFile"]).is_file():
            raise RuntimeError("Install locked dependency before verification: " + package["name"])
    return {"toolchain": "leanprover/lean4:v4.35.0-rc3", "mathlib_rev": mathlib[0]["rev"],
            "installed_dependencies": len(lock["packages"]),
            "dependency_checkout_revisions_independently_checked": False}


def run_lake(arguments, log):
    proc = subprocess.run(["lake", "--no-cache"] + arguments, cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=3600)
    output = scrub(proc.stdout)
    (OUT / log).write_text(output)
    if proc.returncode:
        raise RuntimeError(log + ": Lake/Lean exited " + str(proc.returncode))
    return proc.stdout


def axiom_check():
    source = code_only((ROOT / "verification/Axioms.lean").read_text())
    expected = re.findall(r"^#print axioms (\S+)\s*$", source, re.M)
    if len(expected) != len(set(expected)) or not MAIN_THEOREMS <= set(expected):
        raise RuntimeError("Incomplete or duplicate key axiom probes")
    output = run_lake(["env", "lean", "verification/Axioms.lean"], "axioms.log")
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    rows += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    records = [{"declaration": name, "axioms": sorted(a.strip() for a in axioms.split(",") if a.strip())}
               for name, axioms in rows]
    write_json("axioms.json", records)
    if sorted(r["declaration"] for r in records) != sorted(expected):
        raise RuntimeError("Missing, duplicate or unexpected axiom output")
    if any(set(r["axioms"]) - ALLOWED_AXIOMS for r in records):
        raise RuntimeError("Nonstandard axiom dependency")
    return records


def type_check():
    output = run_lake(["env", "lean", "-Dformat.width=100", "-Dpp.funBinderTypes=true",
                       "verification/Types.lean"], "types.log").strip()
    readme = (ROOT / "README.md").read_text()
    match = re.search(r"<!-- BEGIN MACHINE TYPES -->\s*```text\n(.*?)\n```\s*<!-- END MACHINE TYPES -->",
                      readme, re.S)
    if not match or match.group(1).strip() != output:
        raise RuntimeError("README theorem types differ from current machine output")
    return True


def path_check(paths):
    pattern = re.compile(r"/(?:Users|home)/[A-Za-z0-9_.-]+/|[A-Za-z]:\\Users\\")
    hits = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for match in pattern.finditer(text):
            hits.append({"path": path.relative_to(ROOT).as_posix(),
                         "line": text[:match.start()].count("\n") + 1})
    write_json("public-path-check.json", {"files_checked": len(paths), "hits": hits})
    if hits:
        raise RuntimeError("Machine-specific absolute path in public material")
    return len(paths)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    summary = {"status": "RUNNING", "started_utc": datetime.now(timezone.utc).isoformat(),
               "network_requested": False, "repository_history_required": False,
               "allowed_axioms": sorted(ALLOWED_AXIOMS)}
    try:
        files = public_files()
        paths = [p for p in files if p.suffix == ".lean"]
        summary["lean_files_scanned"] = len(paths)
        summary["frozen_statements"] = frozen_check()
        scan = source_scan(paths)
        summary["forbidden_hits"] = len(scan["forbidden_hits"])
        summary["set_options"] = scan["set_options"]
        coverage = build_coverage(paths)
        summary["default_build_modules"] = coverage["default_build_modules"]
        summary["default_build_project_modules"] = coverage["project_modules"]
        summary["dependencies"] = dependency_preflight()
        candidate = {p.relative_to(ROOT).as_posix(): sha(p) for p in files
                     if OUT not in p.parents}
        write_json("candidate-sha256.json", candidate)
        write_json("summary.json", summary)
        summary["lean_version"] = run_lake(["env", "lean", "--version"], "lean-version.log").strip()
        print("Static checks passed; building all project proofs and audits.", flush=True)
        build = run_lake(["build"], "build.log")
        summary["lake_build_exit_code"] = 0
        summary["build_completion"] = next((line for line in reversed(build.splitlines())
                                           if "Build completed successfully" in line), "")
        if not summary["build_completion"]:
            raise RuntimeError("Lake did not report build completion")
        print("Build passed; checking fresh kernel dependencies and documented types.", flush=True)
        records = axiom_check()
        summary["axiom_declarations_checked"] = len(records)
        summary["key_theorem_axioms"] = {r["declaration"]: r["axioms"] for r in records
                                        if r["declaration"] in MAIN_THEOREMS}
        summary["readme_machine_types_match"] = type_check()
        frozen_check()
        if any(sha(ROOT / name) != digest for name, digest in candidate.items()):
            raise RuntimeError("Candidate files changed during verification")
        summary["public_files_path_checked"] = path_check(public_files())
        summary["status"] = "PASS"
        print("PASS: {} Lean files; {} default-build modules; {} axiom probes; frozen statements and README types match."
              .format(len(paths), coverage["default_build_modules"], len(records)), flush=True)
        return 0
    except Exception as exc:
        summary.update(status="FAIL", error=scrub(str(exc)))
        print("FAIL: " + summary["error"], file=sys.stderr, flush=True)
        return 1
    finally:
        summary["finished_utc"] = datetime.now(timezone.utc).isoformat()
        write_json("summary.json", summary)


if __name__ == "__main__":
    sys.exit(main())
