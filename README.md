# K4 Structure Theory

This repository publishes two bounded Candidates, their preservation map, and
a reproducible Lean 4 companion to the mathematical article:

- [K4 mathematical structure Candidate](./K4-MATHEMATICAL-STRUCTURE-CANDIDATE.md)
- [K4 universal work-structure MVP](./K4-UNIVERSAL-WORK-STRUCTURE-MVP.md)
- [Source-to-destination split map](./SPLIT-MAP.md)
- [Lean 4 formal companion](./lean/README.md)

The mathematical Candidate owns the combinatorial definitions and derivations.
The universal work-structure MVP cites that mathematical authority and does not
specialize the model to Agent Frame. These documents are review Candidates, not
adopted mathematical truth or a stable implementation specification.

The Lean companion deliberately covers only the declarations listed in its own
coverage table. From `lean/`, run `lake build` with the pinned toolchain and
manifest. Candidate extensions about complement singularity, symmetric-group
solvability, or block decomposition are not part of this release.
