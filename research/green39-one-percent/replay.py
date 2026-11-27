"""Compile the accompanying Lean theorems from their pinned sources."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory


SOURCE = Path(__file__).resolve().parent
UPSTREAM = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--in-lake", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    if not args.in_lake:
        for repo, rev in [(checkout, UPSTREAM), (checkout / ".lake/packages/mathlib", MATHLIB)]:
            actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True)
            if actual.strip() != rev:
                raise ValueError(f"Expected {rev} at {repo}")
        command = ["lake", "env", sys.executable, "-B", str(Path(__file__).resolve()),
                   str(checkout), "--in-lake", "--jobs", str(args.jobs)]
        subprocess.run(command, cwd=checkout, check=True)
        return
    files = json.loads((SOURCE / "sha256.json").read_text(encoding="utf-8"))
    sources = {}
    for relative, digest in files.items():
        path = SOURCE / relative
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"Source checksum mismatch for {relative}")
        if path.suffix == ".lean":
            if path.stem in sources:
                raise ValueError(f"Duplicate Lean module {path.stem}")
            sources[path.stem] = path
    imports = {}
    for name, path in sources.items():
        local = set()
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("import "):
                for module in line.split()[1:]:
                    if module.startswith(("Mathlib", "FormalConjectures")):
                        continue
                    if module not in sources:
                        raise ValueError(f"Missing {module} imported by {name}")
                    local.add(module)
        imports[name] = local
    with TemporaryDirectory(prefix="green39-lean-") as tmp:
        build = Path(tmp).resolve()
        env = dict(os.environ)
        inherited = env.get("LEAN_PATH", "").split(os.pathsep)
        env["LEAN_PATH"] = os.pathsep.join([str(build), *[str((checkout / p).resolve())
                                          for p in inherited if p]])
        for name, path in sources.items():
            shutil.copyfile(path, build / f"{name}.lean")
        done = set()
        while len(done) < len(sources):
            ready = sorted(n for n in sources.keys() - done if imports[n] <= done)
            if not ready:
                raise ValueError("Import cycle")
            for name in ready:
                print(f"Compiling {name}", flush=True)
                subprocess.run(["lean", "-j", str(args.jobs), "-DwarningAsError=true", "-o",
                                name + ".olean", name + ".lean"], cwd=build, env=env, check=True)
                subprocess.run(["leanchecker", name], cwd=build, env=env, check=True)
                print(f"Kernel replay passed for {name}", flush=True)
                done.add(name)


if __name__ == "__main__":
    main()
