/-
  Example 2 — A proof is a statement about a model, and you don't deploy
  the model.

  Gap: THE MODEL ERASES THE BUG (refinement / model–reality gap).
  This is the sharpest "verified, still broken" point. It is NOT "the team
  forgot a property." The property is stated, and the proof of it is genuine.
  It is a true theorem about the WRONG mathematical universe — certifying the
  absence of a bug that exists precisely *because* the machine is not ℕ.

  We use UInt8 as a legible stand-in for any fixed-width machine word. The
  argument is identical at 256 bits, just harder to read.
-/
namespace ModelGap

/-
  A vault holding one balance. The safety property we care about: depositing
  money into your account never makes your balance go DOWN. ("No funds vanish
  on deposit.") A more reasonable invariant is hard to imagine.
-/

/-! ### The model: balances are natural numbers. The invariant is a theorem. -/

def depositℕ (balance amount : Nat) : Nat := balance + amount

theorem deposit_never_loses_funds_ℕ (balance amount : Nat) :
    balance ≤ depositℕ balance amount :=
  Nat.le_add_right balance amount

/-! ### Reality: balances are fixed-width words. The identical invariant is
        false — and provably so. The same code, a different universe. -/

def depositWord (balance amount : UInt8) : UInt8 := balance + amount

theorem deposit_CAN_lose_funds_word :
    ¬ (∀ balance amount : UInt8, balance ≤ depositWord balance amount) := by
  intro h
  -- with balance = 255 (full), depositing 1 wraps the balance to 0
  exact absurd (h 255 1) (by decide)

/-- The concrete exploit the ℕ proof "ruled out": a maxed-out account that
    deposits one unit is left holding nothing. -/
example : depositWord 255 1 = 0 := by decide
example : ¬ ((255 : UInt8) ≤ depositWord 255 1) := by decide

/-
  The lesson is not "use a better int type." It is that a proof's force stops
  exactly at the boundary of its model, and that boundary is invisible inside
  the proof. `deposit_never_loses_funds_ℕ` is a perfect, eternal truth about ℕ.
  It says nothing whatsoever about the bytes the machine actually runs.
-/

end ModelGap
