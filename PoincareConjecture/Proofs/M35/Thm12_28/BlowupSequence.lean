import PoincareConjecture.Proofs.M35.Thm12_28.Worldlines
import PoincareConjecture.Proofs.M35.RawFlow.BlowupTimes
import PoincareConjecture.Proofs.M35.Prop12_31.ScalarPositivity









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

variable (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
  (E : RepairedStandardCapExistenceData g₀)
  (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
  (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
  (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)


noncomputable def blowupSequence : GeneralizedBlowupSequence where
  flow _ := generalizedFlow E.flow.base.flow
  base k := ⟨t k, ⟨x k, ht k⟩⟩
  base_scalar_pos k := (E.scalar_pos (ht k) (x k)).trans_eq
    (scalar_eq P E.flow.base.flow (ht k) (x k)).symm
  scalar_diverges := hR.congr' (Eventually.of_forall
    (fun k => (scalar_eq P E.flow.base.flow (ht k) (x k)).symm))



theorem blowupSequence_scale (k : ℕ) :
    (blowupSequence P E t x ht hR).scale k =
      (E.flow.connection (t k)).scalarCurvature (x k) :=
  scalar_eq P E.flow.base.flow (ht k) (x k)



theorem blowupSequence_scaled_time :
    Tendsto (fun k => (blowupSequence P E t x ht hR).scale k * t k) atTop atTop := by
  have heq : (fun k => (blowupSequence P E t x ht hR).scale k * t k) =
      (fun k => (E.flow.base.flow.connection (t k)).scalarCurvature (x k) * t k) := by
    funext k
    exact congrArg (fun R : ℝ => R * t k) (blowupSequence_scale P E t x ht hR k)
  rw [heq]
  exact E.flow.base.tendsto_scalar_mul_time_of_diverges t x ht hR



theorem backwardDuration_le (S : GeneralizedBlowupSequence) (k : ℕ)
    (y : ((S.flow k).slice (S.base k).1).carrier) {mu : ℝ} (hmu : 0 ≤ mu) :
    m30BackwardDuration S k y mu ≤ mu := by
  have hQ : 0 < S.scale k := S.base_scalar_pos k
  have hmax : 0 < max (S.scale k) ((S.flow k).scalar ⟨(S.base k).1, y⟩) :=
    hQ.trans_le (le_max_left _ _)
  exact (div_le_iff₀ hmax).2 (mul_le_mul_of_nonneg_left (le_max_left _ _) hmu)



theorem blowupSequence_worldlines {mu : ℝ} (hmu : 0 ≤ mu) :
    GeneralizedMaximalBackwardFlowLineSurvival (blowupSequence P E t x ht hR) mu := by
  intro A _
  filter_upwards [(blowupSequence_scaled_time P E t x ht hR).eventually_ge_atTop mu]
    with k hk
  intro y _
  exact ⟨maximalWorldlineIco E.flow.base.flow (ht k) y _
    ((blowupSequence P E t x ht hR).base_scalar_pos k) _
    ((backwardDuration_le _ k y hmu).trans hk)⟩

end PoincareConjecture.M35.OrdinaryRealization
