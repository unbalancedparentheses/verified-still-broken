/-
  What formal verification genuinely closes.

  Before the four gaps, the power they are measured against. This is the thing
  a proof does that no test suite can: it closes the implementation/spec gap
  COMPLETELY, across every input at once. The overflow of Example 2 is not an
  indictment of verification — it is what verification PREVENTS, once the word
  type is modeled and the property is stated. A test samples inputs; a proof
  discharges all of them in a single step.
-/
namespace WhatItCloses

/-- A checked addition on machine words: returns `none` exactly when the true
    sum would not fit, and otherwise the (now provably non-wrapping) sum. -/
def checkedAdd (a b : UInt8) : Option UInt8 :=
  if a.toNat + b.toNat < 256 then some (a + b) else none

/-- Verification doing its job: whenever `checkedAdd` succeeds, the result is
    the true mathematical sum — silent wraparound is impossible. The `∀` ranges
    over all 256 × 256 inputs (all 2²⁵⁶ × 2²⁵⁶ at full width), proven at once. -/
theorem checkedAdd_never_wraps (a b r : UInt8) (h : checkedAdd a b = some r) :
    r.toNat = a.toNat + b.toNat := by
  unfold checkedAdd at h
  split at h
  · rename_i hlt
    simp only [Option.some.injEq] at h
    subst h
    rw [UInt8.toNat_add]
    omega
  · contradiction

/-- The exact bug from Example 2 — a balance going DOWN on a deposit — is now
    provably impossible: a successful `checkedAdd` never loses funds. -/
theorem checkedAdd_never_loses (a b r : UInt8) (h : checkedAdd a b = some r) :
    a ≤ r := by
  have := checkedAdd_never_wraps a b r h
  rw [UInt8.le_iff_toNat_le]
  omega

end WhatItCloses
