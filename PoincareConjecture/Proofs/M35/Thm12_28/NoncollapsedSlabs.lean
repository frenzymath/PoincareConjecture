import PoincareConjecture.Proofs.M35.Thm12_28.BlowupSequence
import PoincareConjecture.Proofs.M35.Thm12_28.Noncollapsing

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

variable (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
  (E : RepairedStandardCapExistenceData g₀)
  (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
  (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
  (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
  (N : StandardFlowNoncollapsingCertificate E.flow)

theorem blowupSequence_noncollapsed_at_zero (A : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ y ∈ (blowupSequence P E t x ht hR).baseBall k A,
      GeneralizedKappaNoncollapsedAt ((blowupSequence P E t x ht hR).flow k)
        ⟨((blowupSequence P E t x ht hR).base k).1, y⟩ N.kappa N.radius :=
  Eventually.of_forall (fun k y _ => noncollapsed P E.flow N (ht k) y)

theorem blowupSequence_noncollapsed_slabs (A T : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab (blowupSequence P E t x ht hR) k A T N.kappa N.radius) := by
  let S := blowupSequence P E t x ht hR
  filter_upwards [(blowupSequence_scaled_time P E t x ht hR).eventually_ge_atTop T] with k hk
  have htime : ∀ s ∈ Ioc (-T) 0, t k + s / S.scale k ∈ Ico 0 E.flow.base.lifetime := by
    intro s hs
    exact add_div_mem_Ico_of_mem_Icc (ht k) (S.base_scalar_pos k) hk ⟨hs.1.le, hs.2⟩
  let e := sliceCylinder E.flow.base.flow (ht k) (S.scale k) (S.base_scalar_pos k)
    (Ioc (-T) 0) (S.baseBall k A) htime
  refine ⟨{ embedding := e, zero_identity := ?_, noncollapsed := ?_ }⟩
  · intro h₀ y _
    exact sliceCylinder_zero_identity E.flow.base.flow (ht k) (S.scale k)
      (S.base_scalar_pos k) _ _ htime h₀ y
  · intro s hs y _
    exact noncollapsed P E.flow N (htime s hs) (e.forward s hs y)

end PoincareConjecture.M35.OrdinaryRealization
