/-
  Example 4 — "The theorem checks" is not "the system is verified."

  Gap: THE TRUSTED BASE (axioms, `sorry`, proof shortcuts).
  A Lean proof is sound only relative to the kernel, the axioms in scope, and
  any proof shortcuts used. The crucial fact: the kernel checks the PROOF; it
  does not, and cannot, check whether your axioms are TRUE. That judgment is
  entirely human — and it is where this gap lives. A necessary axiom and a
  false one are the same keyword and the same green checkmark.
-/
namespace TrustedBase

/-! ## 4a. A necessary axiom — real, unavoidable, and possibly wrong.
    Verifying any system that uses cryptography MUST assume properties it
    cannot prove. This is the standard collision-resistance assumption, used
    honestly. Good practice — and still a thing you are trusting, not proving. -/

axiom Hash : Nat → Nat
axiom hash_collision_resistant : ∀ a b, Hash a = Hash b → a = b

theorem ids_are_unique (a b : Nat) (h : Hash a = Hash b) : a = b :=
  hash_collision_resistant a b h

/-! ## 4b. A false axiom that does NOT look false.
    Over ℤ or ℝ, `a * b / b = a` is a theorem; anyone who learned algebra there
    will accept it on sight. Over a fixed-width word it is false, because the
    multiplication overflows. A developer importing ordinary arithmetic
    intuition writes exactly this kind of assumption. -/

axiom mul_div_cancel : ∀ (a b : UInt8), b ≠ 0 → a * b / b = a

/-- A plausible "the fee is always recoverable" theorem, built on it. Green. -/
theorem fee_recoverable (price qty : UInt8) (h : qty ≠ 0) :
    price * qty / qty = price :=
  mul_div_cancel price qty h

/-- But the axiom is false, and Lean will prove THAT too — using only its own
    standard logic (no appeal to the bogus assumption): 200 * 2 = 400 = 144
    (mod 256), and 144 / 2 = 72, not 200. The kernel accepted the axiom and a
    refutation of it, side by side, without complaint. -/
theorem mul_div_cancel_is_false :
    ¬ ∀ (a b : UInt8), b ≠ 0 → a * b / b = a := by
  intro h
  exact absurd (h 200 2 (by decide)) (by decide)

/-! ## 4c. A third hatch: an unproven proof, shipped green.
    Lean does not lie — it emits a warning and records `sorryAx`. Whether that
    fails the build is a CI *policy* decision. "The pipeline is green" means
    "the proof checks AND CI chose not to reject what would have caught this." -/

theorem solvency_preserved
    (assets liabilities : Nat) (h : liabilities ≤ assets) :
    liabilities ≤ assets + 1 := by
  sorry

/-! ## 4d. The only audit that distinguishes them: ask what each checkmark
    actually depends on. This belongs in CI, over every shipped theorem. -/

#print axioms ids_are_unique
-- [Hash, hash_collision_resistant]  ← necessary; must be reviewed by humans
#print axioms fee_recoverable
-- [propext, mul_div_cancel]          ← rests on the false axiom; the kernel raised no objection
#print axioms mul_div_cancel_is_false
-- [propext]                          ← refuted using only Lean's standard logic; the axiom was just wrong
#print axioms solvency_preserved
-- [sorryAx]                          ← unproven; a warning CI may have ignored

end TrustedBase
