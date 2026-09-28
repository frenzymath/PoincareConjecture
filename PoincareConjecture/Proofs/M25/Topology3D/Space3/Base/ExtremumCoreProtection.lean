import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceMorse
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.RetainedCapPlacement

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilySourceAtlas.critical_protected_neighborhood
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (atlas : FamilySourceAtlas original S)
    (horiginal : IsCollarEmbedding original)
    (hgap : ∀ k : Fin r, ∀ p : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ) p = 0 →
      4 * D < |⟪(u : E3), original (p, 0)⟫_ℝ - cut k|)
    (i : Fin n) (q : UnitTwoSphere) (hqCore : q ∈ S.sourceCore i)
    (hqCritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0) :
    let W : Set E3 :=
      {y | ∀ k : Fin r, 2 * D < |⟪(u : E3), y⟫_ℝ - cut k|}
    let U : Set UnitTwoSphere := (atlas.chart i).source ∩
      (fun p : UnitTwoSphere => psi i (p, 0)) ⁻¹' W
    IsOpen W ∧ IsOpen U ∧ q ∈ U ∧ U ⊆ S.sourceCore i ∧
      ∀ a : Fin S.capCount, Disjoint W (S.cap a).cap := by
  let W : Set E3 :=
    {y | ∀ k : Fin r, 2 * D < |⟪(u : E3), y⟫_ℝ - cut k|}
  let U : Set UnitTwoSphere := (atlas.chart i).source ∩
    (fun p : UnitTwoSphere => psi i (p, 0)) ⁻¹' W
  have hW : IsOpen W := by
    have h (k : Fin r) : IsOpen {y : E3 | 2 * D < |⟪(u : E3), y⟫_ℝ - cut k|} :=
      isOpen_lt continuous_const ((continuous_const.inner continuous_id).sub continuous_const).abs
    simpa only [W, ofPred_forall] using isOpen_iInter_of_finite h
  have hU : IsOpen U := (atlas.chart i).open_source.inter
    (hW.preimage (collar_central_contMDiff (psi i) (S.embedding i)).continuous)
  have havoid (a : Fin S.capCount) : Disjoint W (S.cap a).cap := by
    apply disjoint_left.mpr
    intro y hy hcap
    have hb := ((S.cap a).cap_abs_height_bounds y hcap).2.trans (S.cap_removal a)
    rw [S.cap_cut a] at hb
    have hg := hy (S.birth a)
    linarith [S.buffer_pos]
  have hqSource : q ∈ (atlas.chart i).source := atlas.core_subset_source i hqCore
  have hcritical := (atlas.height_critical_iff horiginal i q hqSource).mp hqCritical
  have hcentral : psi i (q, 0) = original (atlas.chart i q, 0) := by
    simpa only [mul_zero] using atlas.collar_eq i q hqSource 0 (by norm_num)
  have hqW : psi i (q, 0) ∈ W := by
    intro k
    rw [hcentral]
    have hg := hgap k (atlas.chart i q) hcritical
    linarith [S.buffer_pos]
  refine ⟨hW, hU, ⟨hqSource, hqW⟩, ?_, havoid⟩
  intro p hp
  apply (S.sourceCore_mem_and_seams.1 i p).mpr
  intro a ha
  exact disjoint_left.mp (havoid a) hp.2 ha.1

end PoincareConjecture.M25.Topology3D
