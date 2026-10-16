# Infinite magma countermodels and an order six equivalence

Axel Abdel Rahamane Meghezzi

Developed with AI assistance. The certificates are checked by Lean.

| Lean certificate | Non-implication | Infinite carrier |
| --- | --- | --- |
| [`E11116/E11116.lean`](E11116/E11116.lean) | `E11116 ⇏ E28770` | Terms over variables indexed by ℕ |
| [`E40909/E40909.lean`](E40909/E40909.lean) | `E40909 ⇏ E28770` | Normal terms containing distinct variables indexed by ℕ |
| [`E48799/E48799.lean`](E48799/E48799.lean) | `E48799 ⇏ E51430` (residual #136) | Two copies of ℕ |

[`A6/A6_Equivalence.lean`](A6/A6_Equivalence.lean) proves that the order six law
`x = y ◇ ((x ◇ ((u ◇ v) ◇ x)) ◇ (y ◇ y))`
is equivalent to `E11116` for every magma. The E11116 countermodel of E28770 therefore also satisfies this law.

## Verification environments

- E11116: [SAIR Stage 2](https://github.com/SAIRcompetition/equational-theories-lean-stage2), commit `4db175c41d917ce39fc82e48c7e440e2a3fa403d`, Lean `v4.32.2`. [`E11116/JudgeProblem.lean`](E11116/JudgeProblem.lean) contains the generated problem interface.
- E40909: [Equational Theories Project](https://github.com/teorth/equational_theories), commit `e5a88a1479011ece4aad8e3c2e7e5c0ebc0a5b2a`, Lean `v4.29.1`.
- E48799: [SAIR Stage 2](https://github.com/SAIRcompetition/equational-theories-lean-stage2), Lean `v4.32.2`. [`E48799/JudgeProblem.lean`](E48799/JudgeProblem.lean) gives the problem interface. The original certificate was accepted by the judge for residual #136; the comment-free version here also compiles locally.
- A6: [SAIR Stage 2](https://github.com/SAIRcompetition/equational-theories-lean-stage2), Lean `v4.32.2`. Run `lake env lean /absolute/path/to/this-repository/A6/A6_Equivalence.lean` from that checkout.

## Check E11116

From the SAIR Stage 2 checkout in Bash or WSL:

```sh
source .env.judge
PROOF_DIR=/absolute/path/to/this-repository/E11116
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$1" -o "$1/JudgeProblem.olean" "$1/JudgeProblem.lean" && lean --root="$1" "$1/E11116.lean"' bash "$PROOF_DIR"
```

## Check E40909

From the Equational Theories checkout:

```sh
lake env lean /absolute/path/to/this-repository/E40909/E40909.lean
```

## Check E48799

From the SAIR Stage 2 checkout in Bash or WSL:

```sh
source .env.judge
PROOF_DIR=/absolute/path/to/this-repository/E48799
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean --root="$1" -o "$1/JudgeProblem.olean" "$1/JudgeProblem.lean" && lean --root="$1" "$1/E48799.lean"' bash "$PROOF_DIR"
```
