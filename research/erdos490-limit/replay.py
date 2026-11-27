"""Replay the hashed Lean sources against the specified formal-conjectures checkout."""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import os
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
TARGET = "Erdos490Limit"


def verify_sources(manifest):
    for relpath, digest in manifest["sha256"].items():
        actual = sha256((HERE / relpath).read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError(f"source digest mismatch for {relpath}")
    print(f"Verified {len(manifest['sha256'])} file digests.", flush=True)


def build(manifest, args, build_dir):
    checkout = Path(args.checkout).resolve()
    for folder, expected in [(checkout, manifest["formal_conjectures"]),
                             (checkout / ".lake/packages/mathlib", manifest["mathlib"])]:
        actual = subprocess.check_output(["git", "-C", folder, "rev-parse", "HEAD"], text=True).strip()
        if actual != expected:
            raise ValueError(f"expected {expected} at {folder}, found {actual}")
    lean = shutil.which("lean")
    checker = shutil.which("leanchecker")
    version = subprocess.check_output([lean, "--version"], text=True, cwd=checkout)
    if manifest["lean_commit"] not in version:
        raise ValueError(f"wrong Lean toolchain: {version}")
    lean_path = os.environ["LEAN_PATH"]
    search = [str(build_dir)] + [
        str((checkout / p).resolve()) if not Path(p).is_absolute() else p
        for p in lean_path.split(os.pathsep) if p
    ]
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(search)}
    graph = manifest["modules"]

    def compile_one(name):
        rel = Path(*name.split(".")).with_suffix(".lean")
        output = (build_dir / rel).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        flags = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false"] if name.startswith("PrimeNumberTheoremAnd.") else []
        if graph[name]["group"] == "local":
            flags += ["-DwarningAsError=true"]
        print(f"Compiling {name}", flush=True)
        run = subprocess.run([lean, "-j", "2", *flags, "-R", HERE / "src",
                              "-o", output, HERE / "src" / rel], cwd=checkout, env=env,
                             capture_output=True, text=True, encoding="utf-8")
        if run.stdout or run.stderr:
            print(run.stdout + run.stderr, flush=True)
        run.check_returncode()
        if name == TARGET:
            for decl in ("transfer", "limit_exists"):
                audit = re.search(rf"'Erdos490Verified\.{decl}' depends on axioms: \[([^\]]+)\]", run.stdout)
                if not audit or set(audit[1].split(", ")) != {"propext", "Classical.choice", "Quot.sound"}:
                    raise RuntimeError(f"unexpected axiom audit for {decl}")
        if name == TARGET or args.replay_all:
            subprocess.run([checker, name], cwd=build_dir, env=env, check=True)
            print(f"Kernel replay passed for {name}", flush=True)

    scheduler = TopologicalSorter({name: data["deps"] for name, data in graph.items()})
    scheduler.prepare()
    pending = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while scheduler.is_active():
            for name in scheduler.get_ready():
                pending[pool.submit(compile_one, name)] = name
            done, _ = wait(pending, return_when=FIRST_COMPLETED)
            for future in done:
                name = pending.pop(future)
                future.result()
                scheduler.done(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", nargs="?", help="path to the pinned formal-conjectures checkout")
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--replay-all", action="store_true", help="also replay each intermediate module")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--in-lake-env", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    verify_sources(manifest)
    if args.check_only:
        return
    if not args.checkout or args.jobs < 1:
        parser.error("supply the checkout path and a positive number of jobs")
    checkout = Path(args.checkout).resolve()
    if not args.in_lake_env:
        cmd = ["lake", "env", sys.executable, str(Path(__file__).resolve()), str(checkout),
               "--jobs", str(args.jobs), "--in-lake-env"]
        if args.replay_all:
            cmd.append("--replay-all")
        subprocess.run(cmd, cwd=checkout, check=True)
        return
    with TemporaryDirectory(prefix="erdos490-lean-") as tmp:
        build(manifest, args, Path(tmp))
    print("Verified Erdos490Verified.limit_exists.", flush=True)


if __name__ == "__main__":
    main()
