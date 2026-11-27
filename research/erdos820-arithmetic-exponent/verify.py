"""Compile and replay the portable Erdős 820 proof in the pinned Lake workspace."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


MODULE = "Erdos820ArithmeticIdentity"
FORMAL_CONJECTURES = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
THEOREMS = (
    "pointwise_bound",
    "arithmetic_identity",
    "common_exponent_iff",
    "site_iff_positive",
)
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def capture(command, project, env):
    return subprocess.run(
        command,
        cwd=project,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        encoding="utf-8",
        check=True,
    ).stdout.strip()


def verify(project, lake):
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)

    if capture(["git", "rev-parse", "HEAD"], project, env) != FORMAL_CONJECTURES:
        raise ValueError(f"Expected Formal Conjectures at {FORMAL_CONJECTURES}")
    if (project / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
        raise ValueError(f"Expected lean-toolchain to specify {TOOLCHAIN}")
    manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(pkg for pkg in manifest["packages"] if pkg["name"] == "mathlib")
    mathlib_dir = project / manifest["packagesDir"] / mathlib["name"]
    if mathlib["rev"] != MATHLIB or capture(
        ["git", "rev-parse", "HEAD"], mathlib_dir, env
    ) != MATHLIB:
        raise ValueError(f"Expected Mathlib at {MATHLIB}")

    lean = [lake, "env", "lean"]
    version = capture([*lean, "--version"], project, env)
    if not version.startswith("Lean (version 4.33.1,"):
        raise ValueError(f"Expected Lean 4.33.1, found {version}")
    print(version, flush=True)

    source = Path(__file__).resolve().with_name(f"{MODULE}.lean")
    with tempfile.TemporaryDirectory(prefix="erdos820-") as temp:
        olean = Path(temp) / f"{MODULE}.olean"
        output = capture(
            [*lean, "-j", "2", "-DwarningAsError=true", "-R", str(source.parent),
             "-o", str(olean), str(source)],
            project,
            env,
        )
        print(output, flush=True)
        reports = re.findall(r"^'([^']+)' depends on axioms: \[([^\]\n]*)\]$", output, re.M)
        actual = {name: set(axioms.split(", ")) for name, axioms in reports}
        expected = {f"Erdos820Identity.{name}": AXIOMS for name in THEOREMS}
        if len(reports) != len(expected) or actual != expected:
            raise ValueError("The four audited theorems must each use exactly the three standard axioms")

        env["LEAN_PATH"] = temp
        subprocess.run([lake, "env", "leanchecker", "--verbose", MODULE],
                       cwd=project, env=env, check=True)
        print(f"Kernel replay and axiom checks passed for {MODULE}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="pinned Formal Conjectures checkout")
    parser.add_argument("--lake", default="lake", help="Lake executable (default: lake on PATH)")
    args = parser.parse_args()
    try:
        verify(args.project.resolve(), args.lake)
    except (OSError, ValueError, subprocess.CalledProcessError, StopIteration) as error:
        if isinstance(error, subprocess.CalledProcessError) and error.stdout:
            print(error.stdout, file=sys.stderr)
        parser.exit(1, f"Verification failed. {error}\n")


if __name__ == "__main__":
    main()
