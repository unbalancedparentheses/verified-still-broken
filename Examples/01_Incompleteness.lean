/-
  Example 1 — A proof only constrains what you remembered to state.

  Gap: SPECIFICATION INCOMPLETENESS.
  Both theorems below are complete, machine-checked, `sorry`-free proofs.
  Both functions are catastrophically wrong. The bug lives entirely in the
  property nobody wrote down.
-/

/-! ## 1a. The warm-up: a verified sort that deletes all your data. -/
namespace Incompleteness

/-- A list is sorted (non-decreasing). -/
inductive Sorted : List Nat → Prop
  | nil  : Sorted []
  | one  : ∀ a, Sorted [a]
  | cons : ∀ a b l, a ≤ b → Sorted (b :: l) → Sorted (a :: b :: l)

/-- The specification we wrote: "the output is sorted." -/
def IsSortingSpec (f : List Nat → List Nat) : Prop := ∀ l, Sorted (f l)

/-- A perfectly useless implementation. -/
def sortBad (_ : List Nat) : List Nat := []

/-- ...and a complete proof that it satisfies the spec, because [] is sorted.
    The missing property — "the output is a permutation of the input" —
    was never stated, so nothing rules this out. -/
theorem sortBad_correct : IsSortingSpec sortBad := by
  intro _; exact Sorted.nil

end Incompleteness

/-! ## 1b. The same hole at a scale where careful teams fall in:
        a transfer proven correct that silently mints to a third party. -/
namespace Incompleteness

structure State where
  alice    : Nat
  bob      : Nat
  deployer : Nat

/-- Spec for `transfer amt`: when Alice has enough funds, Bob gains `amt`
    and Alice's recorded balance decreases by `amt`.
    Note what is NOT said: "and no other balance changes." -/
def TransferSpec (f : Nat → State → State) : Prop :=
  ∀ amt s, amt ≤ s.alice →
    (f amt s).bob = s.bob + amt ∧ (f amt s).alice = s.alice - amt

/-- The stronger property the author meant: the transfer only moves value
    between Alice and Bob. -/
def CompleteTransferSpec (f : Nat → State → State) : Prop :=
  ∀ amt s, amt ≤ s.alice →
    (f amt s).bob = s.bob + amt ∧
    (f amt s).alice = s.alice - amt ∧
    (f amt s).deployer = s.deployer

/-- A malicious transfer that ALSO credits the deployer on every call. -/
def transferEvil (amt : Nat) (s : State) : State :=
  { alice := s.alice - amt, bob := s.bob + amt, deployer := s.deployer + amt }

/-- Fully verified against the spec we wrote. The theft is invisible to it. -/
theorem transferEvil_correct : TransferSpec transferEvil := by
  intro amt s _; exact ⟨rfl, rfl⟩

/-- But the stronger property rejects it immediately. FV did not fail here;
    the written spec did. -/
theorem transferEvil_not_complete : ¬ CompleteTransferSpec transferEvil := by
  intro h
  have hd :=
    (h 1 { alice := 1, bob := 0, deployer := 0 } (by decide)).2.2
  exact Nat.succ_ne_zero 0 hd

end Incompleteness
