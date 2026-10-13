# Lean certificates for E11116 and E40909

Axel Abdel Rahamane Meghezzi

| File | Statement |
| --- | --- |
| [`E11116/E11116.lean`](E11116/E11116.lean) | `E11116 ⇏ E28770` |
| [`E40909/E40909.lean`](E40909/E40909.lean) | `E40909 ⇏ E28770` |

## Verification environments

- E11116: [SAIR Stage 2](https://github.com/SAIRcompetition/equational-theories-lean-stage2), commit `4db175c41d917ce39fc82e48c7e440e2a3fa403d`, Lean `v4.32.2`. [`E11116/JudgeProblem.lean`](E11116/JudgeProblem.lean) contains the generated problem interface.
- E40909: [Equational Theories Project](https://github.com/teorth/equational_theories), commit `e5a88a1479011ece4aad8e3c2e7e5c0ebc0a5b2a`, Lean `v4.29.1`.

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
