import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_Rescaling
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_SlabScalarTransport
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44




theorem regularSlab_initial_inner (F : SurgeryFlowData.{u})
    {a b : ℝ} (S : SurgeryRegularSlab F.slice F.metric a b)
    (x : (F.slice a).carrier) (v w : TangentSpace (𝓡 3) x) :
    (S.flow.metric a).inner x v w = (F.metric a).inner x v w := by
  have hid : (S.identify ⟨a, le_rfl, S.ordered.le⟩ :
      (F.slice a).carrier → (F.slice a).carrier) = id := funext S.initial_identify
  have h := S.metric_pullback ⟨a, le_rfl, S.ordered.le⟩ x v w
  rw [hid, mfderiv_id] at h
  exact h.symm





theorem exists_normalized_regularSlab (P : M44CapPersistencePredecessors.{u})
    (F : SurgeryFlowData.{u}) {a T sigma : ℝ} (hT : 0 < T) (hsigma : 0 < sigma)
    (S : SurgeryRegularSlab F.slice F.metric a (a + T * sigma)) :
    ∃ G : RicciFlow 3 (F.slice a).carrier (Icc 0 T),
      (∀ s x v w, (G.metric s).inner x v w =
        sigma⁻¹ * (S.flow.metric (a + s * sigma)).inner x v w) ∧
      (∀ x v w, (G.metric 0).inner x v w = sigma⁻¹ * (F.metric a).inner x v w) := by
  let I : SpacetimeInterval := {
    domain := Icc a (a + T * sigma)
    ordConnected := ordConnected_Icc
    nontrivial := ⟨a, ⟨le_rfl, S.ordered.le⟩,
      a + T * sigma, ⟨S.ordered.le, le_rfl⟩, S.ordered.ne⟩ }
  obtain ⟨R⟩ := P.ordinary_flow (F.slice a).carrier I S.flow sigma⁻¹ (inv_pos.mpr hsigma) a
  have hsub : Icc (0 : ℝ) T ⊆ (parabolicInterval sigma⁻¹ (inv_pos.mpr hsigma) a I).domain := by
    intro s hs
    apply (mem_parabolicInterval_iff sigma⁻¹ (inv_pos.mpr hsigma) a I s).mpr
    change a ≤ a + s / sigma⁻¹ ∧ a + s / sigma⁻¹ ≤ a + T * sigma
    rw [div_inv_eq_mul]
    exact ⟨le_add_of_nonneg_right (mul_nonneg hs.1 hsigma.le),
      by linarith only [mul_le_mul_of_nonneg_right hs.2 hsigma.le]⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow hsub ordConnected_Icc
    (show (Icc (0 : ℝ) T).Nontrivial from
      ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩)
  have hmetric (s : ℝ) (x : (F.slice a).carrier) (v w : TangentSpace (𝓡 3) x) :
      (G.metric s).inner x v w =
        sigma⁻¹ * (S.flow.metric (a + s * sigma)).inner x v w := by
    dsimp only [G, Poincare.Geometry.RicciFlow.Harnack.restrictFlow]
    simpa only [parabolicTimeInv, div_inv_eq_mul] using R.metric_eq s x v w
  refine ⟨G, hmetric, ?_⟩
  intro x v w
  simpa only [zero_mul, add_zero, regularSlab_initial_inner F S] using hmetric 0 x v w




theorem exists_normalized_regularSlab_for_bound (P : M44CapPersistencePredecessors.{u})
    (F : SurgeryFlowData.{u}) {a T sigma : ℝ} (hT : 0 < T) (hsigma : 0 < sigma)
    (S : SurgeryRegularSlab F.slice F.metric a (a + T * sigma)) :
    ∃ G : RicciFlow 3 (F.slice a).carrier (Icc 0 T),
      (∀ s x v w, (S.flow.metric (a + s * sigma)).inner x v w =
        sigma * (G.metric s).inner x v w) ∧
      (∀ x v w, (G.metric 0).inner x v w = sigma⁻¹ * (F.metric a).inner x v w) := by
  obtain ⟨G, hmetric, hinitial⟩ := exists_normalized_regularSlab P F hT hsigma S
  refine ⟨G, ?_, hinitial⟩
  intro s x v w
  rw [hmetric, ← mul_assoc, mul_inv_cancel₀ hsigma.ne', one_mul]

end PoincareConjecture.M44
