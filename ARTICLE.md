# Formal Verification Moves Trust — It Doesn't Remove It

### A proof relocates risk into the spec, the model, and the trusted base — shown in runnable Lean 4.

I want Ethereum to have more formal verification, not less. That's why I'm writing this.

There's a reliable way to discredit the whole formal-methods effort, and it's to oversell it. Let "formally verified" start to mean "safe," and the first time a verified contract gets drained, everyone walks away with the wrong lesson at the worst possible moment. I'd like to head that off, because the tool is genuinely one of the best we have. It just deserves a sharper claim than the one it usually travels under. The people building Lean models of the protocol are doing some of the most valuable work in the ecosystem, and I want to strengthen the claim their work supports, not chip at it. So take it as given throughout that the team is competent and the methods are mature. The gaps I'm about to point at aren't rookie mistakes. They're what's left after a good team has done everything right.

Here's the claim I'll defend:

> Formal verification shrinks one surface, the gap between an implementation and its specification, almost to zero. What it doesn't do is remove risk. It moves risk elsewhere: into the specification, the model, and the trusted base. The failure mode is to mistake that move for an elimination.

A machine-checked theorem doesn't say "the code is correct." Written out in full it says something more guarded:

> the implementation satisfies the specification, inside a model, modulo a trusted base, for the properties someone thought to state.

The first clause is the part verification actually delivers, and it delivers it completely. Tests and fuzzers sample the space of behaviors; a proof covers all of it. Everything after that first clause is human judgment, and the checkmark doesn't touch any of it. The examples below are each a complete, `sorry`-free Lean 4 proof. (The trusted-base one carries a `sorry` on purpose, which I'll flag when we get there.) Each shows the shape of a real bug living in one of those later clauses. The code compiles, and you can run it yourself.

One objection deserves to be raised straight away, because it runs under the whole piece: *"Every one of these is just the spec or the model or the axioms being wrong, and getting those right is the entire point of the verification program. So you're arguing for the program, not against it."* That's true, and it isn't a rebuttal. Getting the spec, model, and trusted base right is the work. My point is that the work isn't obviously easier than writing correct code in the first place, and that some of it can't be audited from inside the proof at all. The danger is cultural. A team that reads the checkmark as having *finished* that work, rather than relocated it, gets bitten by a bug that technically was never there.

I'm not claiming any of this is new. Each of the four gaps is well understood in the formal-methods literature, and a specialist will recognize all of them on sight. What I want to add is emphasis, plus three concrete things: a small runnable demonstration of each gap, a map onto where this ecosystem actually lost the most money, and the discipline that follows. If there's a novel claim, it's only this: don't let a green checkmark quietly stand in for that work.

---

## First, what verification genuinely closes

The gaps only mean something measured against the power, so start with the power. This is the thing a proof does that no test suite can. Model the machine word, state the property you care about, and the overflow from Section 2 stops being a risk and becomes impossible:

```lean
def checkedAdd (a b : UInt8) : Option UInt8 :=
  if a.toNat + b.toNat < 256 then some (a + b) else none

-- whenever checkedAdd succeeds, the result is the true sum — no silent wrap, ever
theorem checkedAdd_never_wraps (a b r : UInt8) (h : checkedAdd a b = some r) :
    r.toNat = a.toNat + b.toNat := by
  unfold checkedAdd at h
  split at h
  · rename_i hlt; simp only [Option.some.injEq] at h; subst h; rw [UInt8.toNat_add]; omega
  · contradiction
```

The quantifier is doing all the work. That `∀ a b` covers all 256 × 256 inputs here, and all 2²⁵⁶ × 2²⁵⁶ at full width, and the proof settles every one of them at once. A fuzzer can only sample that space. The exact bug Section 2 will exhibit, a balance dropping when you deposit into it, is now unreachable, and provably so:

```lean
theorem checkedAdd_never_loses (a b r : UInt8) (h : checkedAdd a b = some r) :
    a ≤ r := by
  have := checkedAdd_never_wraps a b r h
  rw [UInt8.le_iff_toNat_le]; omega
```

That's not a small thing. A whole class of bug, gone across every possible input, with a certainty testing can't reach. It's why formal verification is worth the trouble, and why it's worth describing accurately. Keep it in mind; the rest of this is about where its reach stops.

---

## 1. A proof only constrains what you thought to say

Start with the simplest version. We say what it means to sort, "the output is sorted," and prove an implementation meets it:

```lean
inductive Sorted : List Nat → Prop
  | nil  : Sorted []
  | one  : ∀ a, Sorted [a]
  | cons : ∀ a b l, a ≤ b → Sorted (b :: l) → Sorted (a :: b :: l)

def IsSortingSpec (f : List Nat → List Nat) : Prop := ∀ l, Sorted (f l)

def sortBad (_ : List Nat) : List Nat := []

theorem sortBad_correct : IsSortingSpec sortBad := by
  intro _; exact Sorted.nil
```

`sortBad` discards your input and returns the empty list. The empty list is sorted, so the proof goes through. What's missing is the requirement that the output be a permutation of the input, and since nobody wrote that down, nothing rules out the cheat. At this size the gap is obvious. The trouble is that the same kind of gap doesn't get any more visible as the system grows. Here it is in a transfer:

```lean
def TransferSpec (f : Nat → State → State) : Prop :=
  ∀ amt s, amt ≤ s.alice →
    (f amt s).bob = s.bob + amt ∧ (f amt s).alice = s.alice - amt

def transferEvil (amt : Nat) (s : State) : State :=
  { alice := s.alice - amt, bob := s.bob + amt, deployer := s.deployer + amt }

theorem transferEvil_correct : TransferSpec transferEvil := by
  intro amt s _; exact ⟨rfl, rfl⟩
```

`transferEvil` debits Alice and credits Bob exactly as the spec demands. It also quietly credits the deployer on every call. The spec pinned down what happens to Alice and Bob and said nothing about anyone else, so the theft is invisible to it.

To be fair, the stronger property catches the cheat at once:

```lean
def CompleteTransferSpec (f : Nat → State → State) : Prop :=
  ∀ amt s, amt ≤ s.alice →
    (f amt s).bob = s.bob + amt ∧
    (f amt s).alice = s.alice - amt ∧
    (f amt s).deployer = s.deployer        -- the clause that was missing

theorem transferEvil_not_complete : ¬ CompleteTransferSpec transferEvil := by
  intro h
  have hd := (h 1 { alice := 1, bob := 0, deployer := 0 } (by decide)).2.2
  exact Nat.succ_ne_zero 0 hd
```

"So write the stronger spec." Right, and good methodology pushes you to. Frame conditions turn "what doesn't change" into an explicit obligation; a full functional-correctness spec tries to pin behavior down completely. That's the correct discipline, and serious teams follow it. But look at what it asks for, and what it can't give back. A spec is often far smaller and clearer than the code it governs, and that's much of the reason to write one. Its completeness is a different question, and that's the one you can't discharge. Listing every property an adversary might reach for, every account that has to stay fixed, every invariant that has to survive every interleaving, is open-ended work. No proof hands you that list, and there's no theorem that says "you've now named everything that matters." Verification stays silent about every property you didn't write down, and that's almost exactly where security bugs live.

---

## 2. A proof is about a model, and you don't ship the model

This is the sharpest of the four, because a better spec won't fix it. The property is stated, the proof is real, and it's still a true theorem about the wrong universe.

Take an invariant nobody would argue with: depositing into your account never lowers your balance. Over the natural numbers it's a theorem:

```lean
def depositℕ (balance amount : Nat) : Nat := balance + amount

theorem deposit_never_loses_funds_ℕ (balance amount : Nat) :
    balance ≤ depositℕ balance amount :=
  Nat.le_add_right balance amount
```

The machine you deploy to doesn't have natural numbers. It has fixed-width words, and they wrap around. The same statement, word for word, is now false, and you can prove it false:

```lean
def depositWord (balance amount : UInt8) : UInt8 := balance + amount

theorem deposit_CAN_lose_funds_word :
    ¬ (∀ balance amount : UInt8, balance ≤ depositWord balance amount) := by
  intro h
  exact absurd (h 255 1) (by decide)         -- 255 + 1 wraps to 0

example : depositWord 255 1 = 0 := by decide
```

A maxed-out account that receives one more unit ends up holding nothing. The proof over ℕ "ruled that out," in a universe where it couldn't happen in the first place. This isn't academic. In 2018 the `batchOverflow` bug (CVE-2018-10299) drained the BeautyChain ERC-20 token through exactly this arithmetic: two transfers of 2²⁵⁵ added up to 2²⁵⁶ and wrapped a 256-bit balance back to zero. A conservation proof over ℕ would have signed off on the vulnerable contract.

Now the obvious objection, and it's fair: no competent team models token arithmetic over ℕ. They use bitvector reasoning that captures the machine word exactly, and this particular bug doesn't survive it. Agreed. But the lesson isn't "pick a better integer type." It's that a proof's reach stops at the edge of its model, and you can't see that edge from inside the proof. `UInt8` here is just a stand-in. Swap in a flawless 256-bit word model and you've only moved the edge somewhere else. The model still leaves something out: the gas schedule, the lowering from source to bytecode, the scheduler, the hardware, the bytes that actually get deployed. A loop you proved terminates can still run out of gas and revert, because cost was never in the model. Two clients that each provably refine the same abstract spec can still split the chain, if the spec left the byte encoding open and they filled it in differently.

There's another gap that no integer type touches, and it's concrete rather than philosophical. A proof about a specification is not a proof about the implementation that runs it. You can verify a protocol in Lean and still have said nothing about the client codebases that execute it, because they aren't extracted from the proof. Good teams know this and work at it, either by verifying clients directly or by running the formal spec as a differential-testing oracle against them. Nobody's unaware of the gap. The point is that closing it is a second effort about as large as the first, and the proof about the spec doesn't do it for you. The bit-precise model closes the arithmetic gap and leaves this one wide open.

This isn't a story about careless people. It's the shape of the field's biggest successes. seL4 and CompCert are verified down to assumptions they state openly, about the compiler, the hardware model, and what's simply out of scope, and the risk that remains sits at those boundaries rather than in the verified core. seL4's documentation is refreshingly direct about it: the non-leakage result holds only for the information channels the hardware model represents, so timing side channels outside that model are out of scope, full stop. CompCert is the encouraging version of the same story. Years of fuzzing turned up no bugs in its verified optimizer, only in the unverified code around it. In both cases the proof did its job, and the boundary was where the attention was owed. The step from "the model I proved things about" to "the system that actually runs" is itself an assumption. You can make it smaller and write it down explicitly, and good practice does, but you can't turn it into a theorem from inside the proof, because the real machine isn't a mathematical object the proof can range over.

---

## 3. "The theorem checks" is not "the system is verified"

A proof is only as sound as the kernel, the axioms in scope, and any shortcuts you took. Here's the fact that carries this section: the kernel checks your proof, but it has no way to check whether your axioms are true. That part is left to people. And a necessary axiom and a ruinous one look identical, same keyword, same green checkmark.

You can't verify anything that uses cryptography without assuming properties you can't prove. That's normal and correct:

```lean
axiom Hash : Nat → Nat
axiom hash_collision_resistant : ∀ a b, Hash a = Hash b → a = b

theorem ids_are_unique (a b : Nat) (h : Hash a = Hash b) : a = b :=
  hash_collision_resistant a b h
```

Now a false axiom, except it doesn't look false. Over the integers or the reals, `a * b / b = a` is just true, and anyone who learned algebra there will nod it through. Over a fixed-width word it's false, because the multiplication overflows:

```lean
axiom mul_div_cancel : ∀ (a b : UInt8), b ≠ 0 → a * b / b = a

theorem fee_recoverable (price qty : UInt8) (h : qty ≠ 0) :
    price * qty / qty = price :=
  mul_div_cancel price qty h
```

Lean accepts the axiom, and the plausible "the fee is always recoverable" theorem sitting on top of it. It will also prove the axiom false, using nothing but its own standard logic, with no help from the bogus assumption:

```lean
theorem mul_div_cancel_is_false : ¬ ∀ (a b : UInt8), b ≠ 0 → a * b / b = a := by
  intro h
  exact absurd (h 200 2 (by decide)) (by decide)   -- 200*2 = 144 (mod 256); 144/2 = 72 ≠ 200
```

So the kernel accepted the axiom and a refutation of that same axiom, side by side, without a word of complaint. It checked the proofs. It never formed an opinion about whether the axiom was true. And that's the realistic danger, not some flagrant `0 = 7` that review would catch on the first pass. It's an axiom that quietly imports intuition from the wrong number system, or describes the environment, a memory model, a cost or timing assumption, and gets it *almost* right. From inside the proof it's indistinguishable from one that's exactly right, and it gets easier to miss as the spec grows. A third hole is quieter still: a proof left unfinished and shipped green.

```lean
theorem solvency_preserved
    (assets liabilities : Nat) (h : liabilities ≤ assets) :
    liabilities ≤ assets + 1 := by
  sorry
```

Lean doesn't lie about that one either. It prints a warning and records `sorryAx`. Whether the warning fails your build is a CI policy decision, not a fact about the proof. "The pipeline is green" can quietly mean "the proof checks, and CI was configured not to reject the thing that would have caught this." The only check that tells the three apart is to ask what each theorem actually rests on:

```lean
#print axioms ids_are_unique
-- [Hash, hash_collision_resistant]  ← necessary; must be reviewed by humans
#print axioms fee_recoverable
-- [propext, mul_div_cancel]          ← rests on the false axiom; the kernel raised no objection
#print axioms mul_div_cancel_is_false
-- [propext]                          ← refuted using only Lean's standard logic; the axiom was just wrong
#print axioms solvency_preserved
-- [sorryAx]                          ← unproven; a warning CI may have ignored
```

"That's malpractice, not a limitation of FV." For the false axiom, sure. But the necessary axiom isn't malpractice. It's unavoidable, and it's every bit as load-bearing and every bit as unprovable. Every verified system rests on a trusted base: the kernel, the elaborator, any use of `native_decide` (which swaps the kernel out for the compiler), and a set of honest assumptions about cryptography and hardware that might be subtly wrong. You don't get to remove the trusted base. You only get to audit it. So the honest statement is an operational one. A verified project is exactly as strong as its axiom policy, its CI policy, and its dependency audit, and the checkmark vouches for none of those.

---

## 4. Verification can't save you from a wrong requirement, only state it precisely

This is the deepest case, and the one that should worry the program most, because the proof is real and the spec looks perfectly reasonable. Take a withdrawal, broken into its two real effects: paying the user, which in a live system is the external call that hands control to a possibly hostile caller, and updating the internal record.

```lean
def pay   (amt : Nat) (w : World) : World := { w with pocketed := w.pocketed + amt }
def debit (amt : Nat) (w : World) : World := { w with recorded := w.recorded - amt }

def WithdrawSpec (before after : World) : Prop :=
  after.pocketed = before.pocketed + before.recorded ∧ after.recorded = 0
```

The spec reads: after withdrawing the full balance, the user has pocketed that balance and is owed nothing. Reasonable enough. Now two implementations, one that pays before it debits and one that debits before it pays:

```lean
def withdrawUnsafe (w : World) : World := let amt := w.recorded; debit amt (pay amt w)
def withdrawSafe   (w : World) : World := let amt := w.recorded; pay amt (debit amt w)

theorem unsafe_meets_spec (w : World) : WithdrawSpec w (withdrawUnsafe w) := by
  refine ⟨?_, ?_⟩ <;> simp [withdrawUnsafe, pay, debit]

theorem safe_meets_spec (w : World) : WithdrawSpec w (withdrawSafe w) := by
  refine ⟨?_, ?_⟩ <;> simp [withdrawSafe, pay, debit]
```

Both satisfy the spec. The verifier is equally happy with either, and "verified" tells you nothing about which one you'd rather deploy. Run them under reentrancy, though, where the attacker re-enters during `pay`, before the record is updated, and they come apart. The property that separates them is the one nobody wrote down:

```lean
-- The attacker re-enters during `pay`, before the record is updated.
def unsafeUnderReentrancy (w : World) : World :=          -- trace: pay; pay; debit; debit
  let amt := w.recorded                                  -- both calls see the same balance
  debit amt (debit amt (pay amt (pay amt w)))

def safeUnderReentrancy (w : World) : World :=            -- debit first ⇒ re-entry sees 0
  let amt := w.recorded
  let w1  := debit amt w
  pay amt (pay w1.recorded (debit w1.recorded w1))

def NoOverWithdrawal (run : World → World) : Prop :=
  ∀ w, (run w).pocketed ≤ w.pocketed + w.recorded

theorem safe_reentrancy_no_overwithdrawal : NoOverWithdrawal safeUnderReentrancy := by
  intro w; simp [safeUnderReentrancy, pay, debit]

theorem unsafe_reentrancy_overwithdraws : ¬ NoOverWithdrawal unsafeUnderReentrancy := by
  intro h
  exact absurd (h { recorded := 100, pocketed := 0 }) (by decide)   -- pockets 200, not 100
```

The safe order provably never overpays. The unsafe one provably does: start it with a recorded balance of 100 and it pays out 200. Both carry a clean proof of the same spec. The whole distance between "fine" and "drained" sat in one unstated assumption, that the external call can't re-enter before the state update, which everyone held in their heads and nobody put in the spec. This is The DAO (June 2016) in miniature, where a reentrant call pulled out roughly 3.6 million ETH by re-entering during the payout, before the balance was written down. The proof wasn't fake. The requirement was incomplete, and verification reproduced it faithfully, hole and all.

"A capable team wouldn't stop at a final-state relation. A trace property, an effect-typed spec, or an explicit adversary allowed to re-enter would all catch this." Granted, and that's the right instinct; the tools exist. But every one of them needs you to decide, up front, to model the external call as a re-entry point an attacker controls. That decision is exactly the knowledge the whole ecosystem was missing in 2016. The property had to be known before it could be written, and the richer the formalism, the more of these choices it asks you to get right. You can't prove your property set is complete. You find out it wasn't, usually after the exploit. Verification turns "is this code correct?" into "have we stated every property that matters?", and the second question doesn't come with a checkmark.

---

## 5. Where this leaves us

I'm not arguing against formal verification. I'm arguing against one way of describing what it buys you.

It does something real and rare. It eliminates the bug class "the code doesn't do what the spec says," completely, across every input the model allows. That class is large and dangerous, and clearing it is worth a great deal of effort. seL4 and CompCert are landmarks precisely because they cleared it for real systems.

What it does is clear that one surface and concentrate the rest of the risk into three places the checkmark doesn't reach:

- the specification, which can be incomplete (§1) or faithfully wrong (§4);
- the model, where you can have a true theorem about the wrong universe, with a refinement gap to the real machine you can't see from inside the proof (§2);
- the trusted base, the axioms the kernel never judges and the CI policy it never sets (§3).

The losses this ecosystem actually suffered line up with those three, not with the implementation-versus-spec gap a proof closes. The DAO was a requirement nobody had finished. The overflow drains would have slipped past a proof done over the wrong arithmetic model, and would have been caught by one done over the right model, which is the whole point about model choice. Consensus splits live on the boundary between a spec and the independent clients that implement it. A green checkmark feels like it has answered all of these. It hasn't, and in the overflow case it only answers if you happened to pick the model that lets it.

So the slogan shouldn't be "formally verified, therefore safe." Closer to the truth:

> Verification turns an open-ended search for bugs into a precise, bounded list of things you still have to get right: the spec, the model, the trusted base. That list is where the real work now lives, and it deserves more scrutiny once the checkmark is green, not less.

In practice that means treating the gaps as part of the verification work, not as footnotes to it:

- Pair every functional spec with its completeness properties: conservation, "nothing else changes," totality, permutation. Keep asking what the spec leaves unconstrained.
- Verify over the type you actually deploy, and put the costs in the model. Failing that, write the refinement to the real machine down as an explicit assumption, and treat that assumption as attack surface.
- Don't let a proof about the spec stand in for a guarantee about the implementation. Verify the client too, or differential-test it against the executable spec. The distance between "the protocol is correct" and "this node is correct" is real work.
- Run `#print axioms` in CI over every theorem you ship, and make the axiom set and the `sorry` policy things a human signs off on.
- Write the unstated assumptions down — atomicity, non-reentrancy, ordering — and prove the properties that depend on them, instead of stopping at the final-state spec.

Do that, and verification delivers what it promises. Treat the checkmark as the finish line and you've traded a real audit for the feeling of one. The tool is excellent. The finish line just sits further out than the checkmark suggests, and saying so plainly is, I think, the best way to help an effort that deserves to work.

---

*All five examples — the positive demonstration above plus the four gaps — are complete Lean 4 source in [`Examples/`](./Examples), and compile under `nix run`. The only warning is the intentional `sorry` in the trusted-base example, whose presence is the point.*

---

### References

- **The DAO (June 2016), reentrancy, ~3.6M ETH** — Gemini Cryptopedia, [*The DAO Hack*](https://www.gemini.com/cryptopedia/the-dao-hack-makerdao); Chainlink, [*Reentrancy Attacks and The DAO Hack*](https://blog.chain.link/reentrancy-attacks-and-the-dao-hack/).
- **`batchOverflow` / BeautyChain (BEC), April 2018** — NVD, [CVE-2018-10299](https://nvd.nist.gov/vuln/detail/CVE-2018-10299).
- **seL4 — what the proofs assume (incl. side channels out of model scope)** — [*What the Proofs Assume*](https://sel4.systems/Verification/assumptions.html).
- **CompCert — trusted computing base** — Monniaux & Boulmé, [*The Trusted Computing Base of the CompCert Verified Compiler*](https://arxiv.org/pdf/2201.10280); fuzzing result: Yang et al., *Finding and Understanding Bugs in C Compilers* (PLDI 2011).
