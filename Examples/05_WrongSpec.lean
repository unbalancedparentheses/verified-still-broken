/-
  Example 5 — Formal verification cannot save you from a wrong requirement.
  It can only make the wrong requirement precise.

  Gap: THE SPEC FAITHFULLY ENCODES THE WRONG IDEA.
  The deepest case, and the most important one to get airtight. The punchline:

      The specification cannot tell the safe implementation apart from the
      unsafe one. BOTH provably satisfy it. One drains under reentrancy and
      one does not — and the spec is silent on the difference.

  This is the abstract shape of the classic reentrancy disaster, with no VM
  in sight. The bug is not in the code and not in the proof; it is an
  assumption (atomicity / "the external call can't re-enter") that the shared
  mental model held but the spec never stated.
-/
namespace WrongSpec

/-- The world: what the contract still owes the user (`recorded`), and what
    the user has actually pocketed (`pocketed`). -/
structure World where
  recorded : Nat
  pocketed : Nat
deriving DecidableEq, Repr

/-- The two real effects of a withdrawal, as separate steps:
    `pay` hands funds to the user — and in a real system this is the external
    call that returns control to the (possibly malicious) caller.
    `debit` updates the contract's internal record. -/
def pay   (amt : Nat) (w : World) : World := { w with pocketed := w.pocketed + amt }
def debit (amt : Nat) (w : World) : World := { w with recorded := w.recorded - amt }

/-- The agreed specification, in plain English: "after a withdrawal of the
    user's full balance, they have pocketed that balance and are owed nothing."
    Note what it does NOT mention: the order of `pay` and `debit`, or what
    happens if `pay` re-enters before `debit`. -/
def WithdrawSpec (before after : World) : Prop :=
  after.pocketed = before.pocketed + before.recorded ∧ after.recorded = 0

/-! ## Two implementations. The spec cannot tell them apart. -/

/-- UNSAFE: pay first, then debit (effects-before-update). -/
def withdrawUnsafe (w : World) : World :=
  let amt := w.recorded
  debit amt (pay amt w)

/-- SAFE: debit first, then pay (the checks-effects-interactions discipline). -/
def withdrawSafe (w : World) : World :=
  let amt := w.recorded
  pay amt (debit amt w)

/-- Both refine the spec. Real, complete proofs. The verifier is satisfied
    by either; "verified ✓" distinguishes nothing. -/
theorem unsafe_meets_spec (w : World) : WithdrawSpec w (withdrawUnsafe w) := by
  refine ⟨?_, ?_⟩ <;> simp [withdrawUnsafe, pay, debit]

theorem safe_meets_spec (w : World) : WithdrawSpec w (withdrawSafe w) := by
  refine ⟨?_, ?_⟩ <;> simp [withdrawSafe, pay, debit]

/-! ## Now run each under reentrancy and watch them diverge. -/

/-- Reentrancy against the UNSAFE order. `pay` returns control to the attacker,
    who calls withdraw AGAIN before `debit` has run — so `recorded` is still
    the full balance and the same amount is paid twice. The honest trace is
    pay;pay;debit;debit (the inner call's debit, then the outer's). -/
def unsafeUnderReentrancy (w : World) : World :=
  let amt := w.recorded            -- both calls see the SAME balance: debit deferred
  debit amt (debit amt (pay amt (pay amt w)))

/-- Reentrancy against the SAFE order. The outer call debits FIRST, so when the
    attacker re-enters, the recorded balance is already 0 and the inner
    withdrawal pays out nothing. -/
def safeUnderReentrancy (w : World) : World :=
  let amt := w.recorded
  let w1  := debit amt w           -- outer debits first: recorded is now 0
  pay amt (pay w1.recorded (debit w1.recorded w1))   -- re-entry sees 0, pays nothing

/-- The unsafe contract is DRAINED: a recorded balance of 100 pays out 200. -/
example : (unsafeUnderReentrancy { recorded := 100, pocketed := 0 }).pocketed = 200 := by
  decide

/-- The safe contract survives the identical attack: it pays out exactly 100. -/
example : (safeUnderReentrancy { recorded := 100, pocketed := 0 }).pocketed = 100 := by
  decide

/-- The missing security property: even under the execution environment the
    contract actually lives in, a withdrawal must not pay more than the balance
    recorded at entry. -/
def NoOverWithdrawal (run : World → World) : Prop :=
  ∀ w, (run w).pocketed ≤ w.pocketed + w.recorded

/-- The safe order satisfies the property under reentrancy. -/
theorem safe_reentrancy_no_overwithdrawal :
    NoOverWithdrawal safeUnderReentrancy := by
  intro w
  simp [safeUnderReentrancy, pay, debit]

/-- The unsafe order does not. This is the property the final-state
    `WithdrawSpec` failed to say. -/
theorem unsafe_reentrancy_overwithdraws :
    ¬ NoOverWithdrawal unsafeUnderReentrancy := by
  intro h
  exact absurd (h { recorded := 100, pocketed := 0 }) (by decide)

/-
  Both implementations carry a flawless proof of the same specification. The
  difference between "fine" and "drained" lives entirely in an ordering
  assumption the specification never made. FV reproduced the requirement with
  perfect fidelity; the requirement was incomplete.
-/

end WrongSpec
