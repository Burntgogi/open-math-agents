"""Lint and replay the seven OMA submissions with the pinned Lean workspace."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
FC = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def output(command, cwd, env=None):
    run = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    if run.returncode:
        raise RuntimeError(run.stdout)
    return run.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("formal", type=Path)
    parser.add_argument("oma", type=Path)
    parser.add_argument("--lint-only", action="store_true")
    parser.add_argument("--in-lake", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    formal, oma = args.formal.resolve(), args.oma.resolve()
    items = json.loads((HERE / "files.json").read_text(encoding="utf-8"))
    for item in items:
        data = (HERE / item["path"]).read_bytes()
        if len(data) != item["bytes"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
            raise ValueError(f"changed source: {item['path']}")
    if not args.in_lake and not args.lint_only:
        for folder, revision in [(formal, FC), (formal / ".lake/packages/mathlib", MATHLIB)]:
            if output(["git", "rev-parse", "HEAD"], folder).strip() != revision:
                raise ValueError(f"unexpected revision at {folder}")
        subprocess.run(["lake", "env", sys.executable, "-B", str(Path(__file__).resolve()),
                        str(formal), str(oma), "--in-lake"], cwd=formal, check=True)
        return
    with TemporaryDirectory(prefix="erdos490-oma-") as build_path:
        build = Path(build_path).resolve()
        for item in items:
            relative = Path(item["path"])
            (build / relative.parent).mkdir(exist_ok=True)
            shutil.copyfile(HERE / relative, build / relative)
        env = os.environ.copy()
        if not args.lint_only:
            roots = [str((formal / p).resolve()) for p in env["LEAN_PATH"].split(os.pathsep) if p]
            env["LEAN_PATH"] = os.pathsep.join([str(build), *roots])
            lean = shutil.which("lean")
            checker = shutil.which("leanchecker")
            version = output([lean, "--version"], formal, env)
            if "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in version:
                raise ValueError(version)
        for i, item in enumerate(items):
            path = Path(item["path"])
            lint = json.loads(output([sys.executable, "-I", oma / "tools/lint.py", path,
                                      oma / "data/catalog.json"], build, env))
            if not lint["ok"]:
                raise ValueError(lint["errors"])
            print(f"Lint passed for {path.name}", flush=True)
            if args.lint_only:
                continue
            module = lint["module"] if lint["type"] == "reduction" else f"PublicStep{i}"
            name = lint["theorem"]
            source = Path(*module.split(".")).with_suffix(".lean")
            (build / source.parent).mkdir(exist_ok=True, parents=True)
            shutil.copyfile(build / path, build / source)
            output([lean, "-j", "2", "-DwarningAsError=true", "-o",
                    source.with_suffix(".olean"), source], build, env)
            expected = ""
            if lint["type"] != "reduction":
                root, step = path.stem.rsplit(".", 1)
                expected = f"example : OMA.R_{root.replace('.', '_')}.{step} := {name}\n"
            inspect = build / "Audit.lean"
            inspect.write_text(f"import {module}\n/-! Kernel audit. -/\n{expected}#print axioms {name}\n",
                               encoding="utf-8")
            report = output([lean, "-j", "2", "-DwarningAsError=true", inspect.name], build, env)
            match = re.search(rf"'{re.escape(name)}' depends on axioms: \[([^\]]+)\]", report)
            if not match or set(match[1].split(", ")) != ALLOWED:
                raise RuntimeError(report)
            output([checker, module], build, env)
            print(f"Kernel replay passed for {module}: {report.strip()}", flush=True)
        if not args.lint_only:
            shutil.copyfile(HERE / "Hierarchy.lean", build / "Hierarchy.lean")
            output([lean, "-j", "2", "-DwarningAsError=true", "-o", "Hierarchy.olean",
                    "Hierarchy.lean"], build, env)
            output([checker, "Hierarchy"], build, env)
            print("The two reductions compose at the exact type of the site statement.", flush=True)


if __name__ == "__main__":
    main()
