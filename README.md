# verified-still-broken

Five small Lean 4 examples that type-check under the project runner — with one intentional `sorry` warning. One shows what verification genuinely closes; the other four each sit on top of the shape of a real bug. They accompany the essay [*A Proof Is Only as Good as Its Spec*](https://federicocarrone.com/articles/formal-verification-moves-trust/).

The point is not that formal verification fails. In every example, Lean succeeds exactly: the theorem is true. The bug lives in the *human boundary* around the proof — the specification, the model, or the trusted base. The essay's thesis:

> Formal verification shrinks one surface — the gap between implementation and specification — to nearly zero. It does not remove risk; it **relocates** the remaining risk into the specification, the model, and the trusted base. The danger is treating that relocation as elimination.

These examples are deliberately minimal and domain-general; the connection to Ethereum is drawn in the prose, not the code.

## Run it

```sh
nix run        # type-check all five examples
nix develop    # drop into a shell with `lean` on PATH
```

Requires Nix with flakes enabled. Pinned to Lean 4.29.1 via the flake.

## The examples

| File | What it shows | Detail |
|------|---------------|--------|
| [`00_WhatItCloses`](./Examples/00_WhatItCloses.lean) | What FV genuinely closes | A checked addition proven to *never* silently wrap, for **all** inputs at once — the overflow class eliminated with a certainty testing can't reach. The power the rest is measured against. |
| [`01_Incompleteness`](./Examples/01_Incompleteness.lean) | The spec says too little | A `sort` proven "always sorted" returns `[]`; a `transfer` proven to debit/credit correctly also mints to a third party. The stronger spec (`CompleteTransferSpec`) is shown to reject it — FV didn't fail, the spec did. |
| [`02_ModelGap`](./Examples/02_ModelGap.lean) | The model erases the bug | "A deposit never decreases your balance" is a **theorem over `ℕ`** and **provably false over `UInt8`** (255 + 1 = 0). Same statement, wrong universe. |
| [`04_TrustedBase`](./Examples/04_TrustedBase.lean) | The trusted base is unaudited | A *necessary* axiom, a *false* one, and a `sorry` all produce green checkmarks. `#print axioms` is the only thing that tells them apart — the kernel checks proofs, not the truth of axioms. |
| [`05_WrongSpec`](./Examples/05_WrongSpec.lean) | The spec encodes the wrong idea | A safe and an unsafe withdrawal **both satisfy the same spec**; only the stronger `NoOverWithdrawal` separates them, and the unsafe one provably drains under reentrancy. |

## The one expected warning

`04_TrustedBase` emits `declaration uses 'sorry'` and prints its axiom dependencies. That is the demonstration, not a defect:

```
'TrustedBase.ids_are_unique'           depends on axioms: [Hash, hash_collision_resistant]
'TrustedBase.fee_recoverable'          depends on axioms: [propext, mul_div_cancel]
'TrustedBase.mul_div_cancel_is_false'  depends on axioms: [propext]
'TrustedBase.solvency_preserved'       depends on axioms: [sorryAx]
```

Every other file type-checks with no diagnostics.
