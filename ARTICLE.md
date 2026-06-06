# Formal Verification Moves Trust — It Doesn't Remove It

### A proof relocates risk into the spec, the model, and the trusted base — shown in runnable Lean 4.

I want Ethereum to have more formal verification, not less. That is why I am writing this.

The fastest way to discredit the formal-methods program is to oversell it — to let "formally verified" come to mean "safe," and then watch the first verified-and-drained contract teach everyone the wrong lesson at the worst possible time. Formal verification is one of the most powerful tools we have. It deserves a precise claim, and the precise claim is narrower and more useful than the slogan it usually travels under. The researchers building Lean models of the protocol are doing some of the most valuable work in the ecosystem, and my aim is to sharpen the claim their work supports, not to diminish it. Everything that follows assumes a competent team using mature methodology: the gaps I point at are not mistakes such a team would make, but limits that remain after it has done everything right.

Here is the claim I will defend:

> Formal verification shrinks one surface — the gap between the implementation and its specification — to nearly zero. It does not remove risk; it **relocates** the remaining risk into the specification, the model, and the trusted base. The danger is treating that relocation as elimination.

A machine-checked theorem does not say "the code is correct." Spelled out, it says:

> **the implementation satisfies the specification — inside a model — modulo a trusted base — for the properties someone thought to state.**

The first clause is what verification actually delivers, and it delivers it completely: tests and fuzzers sample the behavior space; a proof closes it. Every clause *after* the first is human judgment that the green checkmark does not check. The four examples below are each a complete, `sorry`-free Lean 4 proof (the trusted-base one is `sorry`-free except where the `sorry` is the point), and each demonstrates the shape of a real bug that can live in one of those later clauses. The code compiles; you can run it.

The objection I most want to take seriously runs through the whole piece, so let me state it now: *"Every one of these is the spec or the model or the axioms being wrong — and getting those right is exactly what the verification program is for. So this is an argument for the program, not against it."* That is correct, and it is not a rebuttal. The program *is* the work of getting the spec, model, and trusted base right. The point is that this work is not obviously easier than writing correct code — and in places it is structurally unauditable from inside the proof. A culture that reads the checkmark as having *discharged* that work, rather than *relocated* it, will get hurt by a bug that was, technically, never there.

None of the four gaps below is a new discovery — each is well understood in the formal-methods literature, and a specialist will recognize all of them. I am not offering a theorem; I am offering an emphasis: a small, runnable demonstration of each gap, a mapping onto where this ecosystem's largest losses actually happened, and the operational discipline that follows. The only claim to novelty is the refusal to let a green checkmark quietly stand in for that work.

---

## First: what verification genuinely closes

The gaps only matter relative to the power, so begin with the power — the thing a proof does that no test suite can. Model the machine word, state the property, and the overflow from Section 2 stops being a risk and becomes an impossibility:

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

The quantifier is the whole point. That `∀ a b` ranges over all 256 × 256 inputs here, and all 2²⁵⁶ × 2²⁵⁶ at full width — and the proof discharges every one of them in a single step. A fuzzer samples that space; a proof closes it. The exact bug Section 2 will exhibit, a balance falling on a deposit, is now provably unreachable:

```lean
theorem checkedAdd_never_loses (a b r : UInt8) (h : checkedAdd a b = some r) :
    a ≤ r := by
  have := checkedAdd_never_wraps a b r h
  rw [UInt8.le_iff_toNat_le]; omega
```

This is not a small thing. An entire class of bug, eliminated across every input, with a certainty no amount of testing can buy. That is what makes formal verification worth the effort — and worth getting the framing right. Hold onto it; everything that follows is about where its reach ends.

---

## 1. A proof only constrains what you remembered to state

Start with the cleanest case. We specify what it means to sort — "the output is sorted" — and prove an implementation meets it:

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

`sortBad` throws away all of your data and returns the empty list, which is sorted, so the proof goes through. The missing property — that the output is a *permutation* of the input — was never stated, and nothing rules it out. In a function this small the omission is obvious. The point is that the *category* of error does not get more visible as the system grows. Here is the same hole in a transfer:

```lean
def TransferSpec (f : Nat → State → State) : Prop :=
  ∀ amt s, amt ≤ s.alice →
    (f amt s).bob = s.bob + amt ∧ (f amt s).alice = s.alice - amt

def transferEvil (amt : Nat) (s : State) : State :=
  { alice := s.alice - amt, bob := s.bob + amt, deployer := s.deployer + amt }

theorem transferEvil_correct : TransferSpec transferEvil := by
  intro amt s _; exact ⟨rfl, rfl⟩
```

`transferEvil` debits Alice and credits Bob exactly as specified — and *also* mints to the deployer on every call. The spec said what happens to Alice and Bob; it never said "and no other balance changes." The theft is invisible to it.

The honest part is that the stronger property catches it immediately:

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

*"So write the stronger spec."* Yes — and mature methodology pushes hard in exactly that direction. Frame conditions make "what does not change" an explicit proof obligation; a full functional-correctness specification aims to pin behavior down completely. This is the right discipline, and serious teams practice it. But notice what it asks, and what it cannot provide. A specification can be far smaller and clearer than the code it governs — that is much of the value of writing one. Its *completeness*, though, is a separate matter, and it is the unverifiable one: enumerating every property an adversary could exploit — every account that must not change, every invariant that must hold across every interleaving — is open-ended work that no proof discharges for you. There is no theorem stating "you have now listed all the properties that matter." Verification is silent on every property you did not write down, and security bugs live, almost by definition, in the properties nobody thought to write down.

---

## 2. A proof is a statement about a model, and you don't deploy the model

This is the sharpest case, because it is not fixable by writing a better spec. The property is stated, the proof is genuine — and it is a true theorem about the wrong universe.

Take the most reasonable invariant imaginable: depositing money into your account never makes your balance go down. Over the natural numbers, it is a theorem:

```lean
def depositℕ (balance amount : Nat) : Nat := balance + amount

theorem deposit_never_loses_funds_ℕ (balance amount : Nat) :
    balance ≤ depositℕ balance amount :=
  Nat.le_add_right balance amount
```

The machine you deploy to does not have natural numbers. It has fixed-width words, and they wrap. The *identical* statement is now false — provably:

```lean
def depositWord (balance amount : UInt8) : UInt8 := balance + amount

theorem deposit_CAN_lose_funds_word :
    ¬ (∀ balance amount : UInt8, balance ≤ depositWord balance amount) := by
  intro h
  exact absurd (h 255 1) (by decide)         -- 255 + 1 wraps to 0

example : depositWord 255 1 = 0 := by decide
```

A maxed-out account that receives one unit is left holding nothing. The ℕ proof "ruled this out" — in a universe where it cannot happen. This is not a toy concern: the 2018 `batchOverflow` bug (CVE-2018-10299) drained the BeautyChain ERC-20 token through exactly this arithmetic, when two transfers of 2²⁵⁵ summed to 2²⁵⁶ and wrapped a 256-bit balance counter back to zero. A proof of conservation over ℕ would have certified the vulnerable contract as safe.

Now, the necessary concession, because it is the one a serious reader reaches for instantly: *no competent team verifies token arithmetic over ℕ.* They model the machine word precisely, with bitvector reasoning, and this specific bug does not survive. Correct. But the lesson is not "use a better integer type." The lesson is that a proof's force stops exactly at the boundary of its model, and **that boundary is invisible from inside the proof.** `UInt8` is a stand-in; replace it with a perfect 256-bit word model and you have only moved the boundary. The model still omits *something* — the gas schedule, the compiler's lowering to bytecode, the scheduler, the hardware, the actual deployed artifact. A loop you prove terminates can still run out of gas and revert, because your model had no notion of cost. Two clients that each provably refine the same abstract spec can still fork the chain, because the spec abstracted away the byte encoding where they disagree.

There is also a gap that no choice of integer type touches at all, and it is concrete rather than philosophical: a proof about a *specification* of a system is not a proof about the *implementation* that runs it. You can verify a protocol in Lean and have said nothing yet about the independent client codebases that actually execute it — they are not extracted from the proof. Good teams know this and work to close it, by verifying clients directly or by using the formal spec as a differential-testing oracle against them. The point is not that anyone is unaware of the gap; it is that closing it is a second, comparably large effort, and the proof about the spec does not perform it. The bit-precise model closes the arithmetic gap and leaves this one untouched.

This is not a hypothetical failure of careless people. It is the explicit shape of the field's landmark successes. seL4 and CompCert are verified *down to stated assumptions* about the compiler, the hardware model, and what is out of scope — and the residual risk lives at exactly those boundaries, not in the verified core. seL4's own documentation is admirably blunt about this: its non-leakage result holds only for the information channels its hardware model represents, so timing side channels outside that model are simply out of scope. CompCert tells the encouraging mirror image of the same story — extensive fuzzing campaigns found no bugs in its verified optimizer, only in the unverified code around it. In both cases the proof held perfectly and the boundary was where attention was owed. The refinement from "the model I proved things about" to "the system that runs" is itself an assumption: you can make it smaller and more explicit, and good practice does exactly that, but you cannot make it a theorem from inside the proof, because the real machine is not a mathematical object your proof can quantify over.

---

## 3. "The theorem checks" is not "the system is verified"

A proof is sound relative to the kernel, the axioms in scope, and any shortcuts taken. The load-bearing fact: **the kernel checks the proof; it does not, and cannot, check whether your axioms are true.** That is human work, and a necessary axiom and a catastrophic one are the same keyword and the same green checkmark.

You cannot verify a system that uses cryptography without assuming properties you cannot prove. This is correct, standard practice:

```lean
axiom Hash : Nat → Nat
axiom hash_collision_resistant : ∀ a b, Hash a = Hash b → a = b

theorem ids_are_unique (a b : Nat) (h : Hash a = Hash b) : a = b :=
  hash_collision_resistant a b h
```

Now a false axiom — but notice that it does not *look* false. Over the integers or the reals, `a * b / b = a` is a theorem; anyone who learned algebra there will accept it on sight. Over a fixed-width machine word it is false, because the multiplication overflows:

```lean
axiom mul_div_cancel : ∀ (a b : UInt8), b ≠ 0 → a * b / b = a

theorem fee_recoverable (price qty : UInt8) (h : qty ≠ 0) :
    price * qty / qty = price :=
  mul_div_cancel price qty h
```

Lean accepts the axiom and the plausible "the fee is always recoverable" theorem built on it. It will *also* prove the axiom false — and that refutation leans on nothing but Lean's own standard logic, not on the bogus assumption:

```lean
theorem mul_div_cancel_is_false : ¬ ∀ (a b : UInt8), b ≠ 0 → a * b / b = a := by
  intro h
  exact absurd (h 200 2 (by decide)) (by decide)   -- 200*2 = 144 (mod 256); 144/2 = 72 ≠ 200
```

The kernel accepted the assumption and a refutation of it, side by side, without complaint. It validated the proofs; it never had an opinion about whether the axiom was true. And this is the realistic danger, not a blatant falsehood that review would catch: an axiom that imports intuition from the wrong number system, or models the environment — a memory model, a cost or timing assumption — and is *almost* right. Inside the proof it is indistinguishable from one that is exactly right, and it grows steadily easier to overlook as the specification grows. A third hatch is subtler still: an unfinished proof shipped green.

```lean
theorem solvency_preserved
    (assets liabilities : Nat) (h : liabilities ≤ assets) :
    liabilities ≤ assets + 1 := by
  sorry
```

Lean does not lie about this either — it emits a warning and records `sorryAx`. Whether that warning fails your build is a CI *policy* decision, not a property of the proof. "The pipeline is green" can mean "the proof checks *and* CI chose not to reject what would have caught this." The only audit that separates the three is to ask what each checkmark actually depends on:

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

*"That's malpractice, not a limitation of FV."* The false axiom, yes. But the *necessary* one is not malpractice — it is unavoidable, and it is just as load-bearing and just as unprovable. Every verified system rests on a trusted base: the kernel, the elaborator, any `native_decide` (which trades the kernel for the compiler), and a set of honest axioms about cryptography and hardware that could be subtly wrong. You cannot eliminate the trusted base; you can only audit it. So the correct statement is operational: **a verified project is only as strong as its axiom policy, its CI policy, and its dependency audit** — none of which the checkmark verifies for you.

---

## 4. Verification cannot save you from a wrong requirement — only make it precise

The deepest case, and the one that should worry the program most, because the proof is real *and* the specification is reasonable. Consider a withdrawal, decomposed into its two real effects — paying the user (in a real system, the external call that hands control to a possibly-malicious caller) and updating the internal record:

```lean
def pay   (amt : Nat) (w : World) : World := { w with pocketed := w.pocketed + amt }
def debit (amt : Nat) (w : World) : World := { w with recorded := w.recorded - amt }

def WithdrawSpec (before after : World) : Prop :=
  after.pocketed = before.pocketed + before.recorded ∧ after.recorded = 0
```

The spec says: after a withdrawal of the full balance, the user has pocketed that balance and is owed nothing. Reasonable. Now two implementations — one pays before debiting, one debits before paying:

```lean
def withdrawUnsafe (w : World) : World := let amt := w.recorded; debit amt (pay amt w)
def withdrawSafe   (w : World) : World := let amt := w.recorded; pay amt (debit amt w)

theorem unsafe_meets_spec (w : World) : WithdrawSpec w (withdrawUnsafe w) := by
  refine ⟨?_, ?_⟩ <;> simp [withdrawUnsafe, pay, debit]

theorem safe_meets_spec (w : World) : WithdrawSpec w (withdrawSafe w) := by
  refine ⟨?_, ?_⟩ <;> simp [withdrawSafe, pay, debit]
```

**Both satisfy the spec.** The verifier is equally happy with either; "verified ✓" distinguishes nothing between them. But run each under reentrancy — the attacker re-enters during `pay`, before the record is updated — and they diverge. The missing property is the one nobody wrote down:

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

The safe order provably never over-withdraws. The unsafe order provably does — a recorded balance of 100 pays out 200. Both carried a flawless proof of the same specification. The entire difference between "fine" and "drained" lived in an ordering assumption — *the external call cannot re-enter before the state update* — that the shared mental model held and the spec never stated. This is the abstract shape of The DAO (June 2016), where a reentrant call drained roughly 3.6 million ETH by re-entering during the payout, before the balance was written down. It is the point in its purest form: the proof was not fake. The requirement was incomplete. Formal verification reproduced the requirement with perfect fidelity, including its hole.

*"A capable team would not stop at a final-state relation — a trace property, an effect-typed specification, or an explicit adversary permitted to re-enter would all expose this."* Conceded; that is the right instinct, and the tools to express it exist. But each of them requires deciding, in advance, to model the external call as an adversarial re-entry point — and that decision is precisely the knowledge the entire ecosystem lacked in 2016. The hard problem, stated plainly: the property had to be *known* to be written, and the richer the formalism, the more such choices it asks you to get right. The completeness of your property set is not something you can prove; it is something you discover, often after the exploit. Verification turns "is this code correct?" into "have we stated every property that matters?" — and the second question has no green checkmark.

---

## 5. The honest conclusion

None of this is an argument against formal verification. It is an argument against a framing.

Verification does something real and rare: it eliminates the bug class "the code does not do what the spec says," completely, across all inputs the model admits. That class is large and dangerous, and closing it is worth enormous effort. seL4 and CompCert are landmark achievements precisely because they closed it for real systems.

But it shrinks *that* surface and **concentrates the remaining risk** into three places the checkmark does not touch:

- **the specification** — incomplete (§1) or faithfully wrong (§4),
- **the model** — true theorems about the wrong universe, with a refinement gap to the real machine that is invisible from inside the proof (§2),
- **the trusted base** — axioms the kernel never judges, and CI policy it never sets (§3).

The bugs that actually drained value from this ecosystem map onto those three places, not onto the implementation/spec gap a proof closes: The DAO's reentrancy was a requirement nobody had completed; the integer-overflow drains would have survived a proof conducted over the wrong arithmetic model (and would have been *caught* by one over the right one — which is exactly the point about model choice); consensus splits live at the boundary between a spec and the independent clients that implement it. A green checkmark *feels* like it has spoken to all of these. It has not — and in the overflow case it speaks only if you chose the model that lets it.

So the slogan should not be "formally verified, therefore safe." It should be:

> Verification converts an open-ended search for bugs into a precise, bounded set of things you must still get right — the spec, the model, the trusted base. That set is now the entire game, and it deserves more scrutiny after the checkmark, not less.

Concretely, that means treating the gaps as first-class parts of the verification effort, not afterthoughts:

- **Pair every functional spec with its completeness properties** — conservation, "nothing else changes," totality, permutation. Ask what the spec does *not* constrain.
- **Verify over the deployment type and model the costs**, or state the refinement to the real machine as an explicit, reviewed assumption — and treat that assumption as attack surface.
- **Don't let a spec proof stand in for an implementation guarantee** — verify the client too, or differential-test it against the executable spec; the gap between "the protocol is correct" and "this node is correct" is real work, not a formality.
- **Put `#print axioms` in CI**, over every shipped theorem; make the axiom set and the `sorry` policy things humans sign off on.
- **Write down the unstated assumptions** — atomicity, non-reentrancy, ordering — and prove the properties that depend on them, not just the final-state spec.

Do that, and verification delivers the safety it promises. Treat the checkmark as the finish line, and it risks substituting the feeling of certainty for the audit that certainty still requires. The tool is excellent; the finish line is simply further out than a green checkmark suggests. Naming that distance plainly is, I think, the surest way to help a program that deserves to succeed.

---

*All five examples — the positive demonstration above plus the four gaps — are complete Lean 4 source in [`Examples/`](./Examples), and compile under `nix run`. The only warning is the intentional `sorry` in the trusted-base example, whose presence is the point.*

---

### References

- **The DAO (June 2016), reentrancy, ~3.6M ETH** — Gemini Cryptopedia, [*The DAO Hack*](https://www.gemini.com/cryptopedia/the-dao-hack-makerdao); Chainlink, [*Reentrancy Attacks and The DAO Hack*](https://blog.chain.link/reentrancy-attacks-and-the-dao-hack/).
- **`batchOverflow` / BeautyChain (BEC), April 2018** — NVD, [CVE-2018-10299](https://nvd.nist.gov/vuln/detail/CVE-2018-10299).
- **seL4 — what the proofs assume (incl. side channels out of model scope)** — [*What the Proofs Assume*](https://sel4.systems/Verification/assumptions.html).
- **CompCert — trusted computing base** — Monniaux & Boulmé, [*The Trusted Computing Base of the CompCert Verified Compiler*](https://arxiv.org/pdf/2201.10280); fuzzing result: Yang et al., *Finding and Understanding Bugs in C Compilers* (PLDI 2011).
