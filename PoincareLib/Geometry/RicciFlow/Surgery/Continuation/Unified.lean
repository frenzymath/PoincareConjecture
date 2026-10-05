import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.UnifiedTheory

/-!
Adapted from Mapher `PoincareMT/Proofs/M43.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M43 logical continuation-branch assembly

The M41 and M42 services select a terminal constructor on one supplied M33
branch. This entry packages their result in the existing disjoint sum.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-
Fix M41 and M42 services, a preterminal input I, and one concrete M33 branch
B. Return the nonempty or vanishing certificate for exactly I and B inside
RepairedUnifiedContinuationData. Each certificate retains its operation,
constructor equality, post-terminal interval, admissibility and pinching.

Logical derivation: inspect I's supplied controlled-core status. Apply M41
in the nonempty case and M42 in the empty case, then insert the obtained
witness into the appropriate Sum constructor. No branch is reselected.

This is a logical assembly, not an independent Morgan--Tian theorem.
The geometric continuation remains the M33 obligation from Lemma 15.11
(printed p. 364) and the degenerate Theorem 15.9 case (pp. 409--410).
`reviews/errata/2026-09-14-local-continuation-controls.md` reserves the later
canonical and noncollapsing propagation for Chapters 16--17.
-/
theorem repairedUnifiedContinuation : RepairedUnifiedContinuationTheory.{u} := by
  refine ⟨?_⟩
  intro N V F T I branch
  cases I.core_status with
  | nonempty hcore =>
      rcases N.continuation I branch hcore with ⟨continuation⟩
      exact ⟨⟨Sum.inl continuation⟩⟩
  | empty hcore =>
      rcases V.continuation I branch hcore with ⟨continuation⟩
      exact ⟨⟨Sum.inr continuation⟩⟩

end PoincareMT
