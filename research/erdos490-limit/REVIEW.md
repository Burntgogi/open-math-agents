# A Lean proof of the Erdős 490 limit

For finite sets A,B in {1,…,N} with multiplication injective on A × B, let M(N) be the greatest possible |A||B|. The sequence M(N) log(N)/N² converges to a finite real number. The exact value of the limit is open.

The theorem `Erdos490Verified.limit_exists` in [Erdos490Limit.lean](src/Erdos490Limit.lean) has the exact type of the pinned formal-conjectures statement. The proof of step H2 is `Erdos490Verified.transfer`. Both use only `propext`, `Classical.choice`, and `Quot.sound`. The [verification receipt](original-axiom-audit.txt) records the kernel replay.

With Git, Python 3.10+ and Lean 4.33.1 installed, run these commands from this directory.

~~~sh
python replay.py --check-only
git clone https://github.com/google-deepmind/formal-conjectures.git
git -C formal-conjectures checkout 9097e2f90e66d2f6244209cb1c07f7120d17ec53
cd formal-conjectures
lake exe cache get
lake build FormalConjectures/ErdosProblems/490.lean:olean
cd ..
python replay.py formal-conjectures --jobs 2
~~~

The last command compiles the proof into a fresh temporary directory and replays the final theorem with `leanchecker`. Add `--replay-all` to replay each intermediate module as well. [Source hashes and dependencies](manifest.json) · [Proof outline and credits](README.md)
