import PoincareConjecture.Proofs.M11.HorizontalLinear





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem box_inverse_smooth (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    letI := intervalChartedSpace (A.box b).interval
    letI := adaptedChartedSpace A
    ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞
      (boxHomeomorph (A.box b)).symm (boxHomeomorph (A.box b)).target :=
  cover_inverse_smooth (fun b ↦ boxHomeomorph (A.box b))
    (box_targets_cover A) (box_transition_smooth A) b

theorem box_inverse_mfderiv (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (p : X) (hp : p ∈ (boxHomeomorph (A.box b)).target) (v : SpacetimeModelVector n) :
    letI := intervalChartedSpace (A.box b).interval
    letI := adaptedChartedSpace A
    (boxTangentEquiv A b ((boxHomeomorph (A.box b)).symm p)).symm v =
      mfderiv (spacetimeModel n) (spacetimeModel n) (boxHomeomorph (A.box b)).symm p v := by
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  let q := (boxHomeomorph (A.box b)).symm p
  have hinv := (box_inverse_smooth A b).contMDiffAt
    ((boxHomeomorph (A.box b)).open_target.mem_nhds hp)
  have heq : (A.box b).toSpacetime ∘ (boxHomeomorph (A.box b)).symm =ᶠ[𝓝 p] id := by
    filter_upwards [(boxHomeomorph (A.box b)).open_target.mem_nhds hp] with x hx
    exact boxHomeomorph_right_inv (A.box b) hx
  have hchain := mfderiv_comp_apply p
    (((adapted_box_localDiffeomorph A b).contMDiff q).mdifferentiableAt (by simp))
    (hinv.mdifferentiableAt (by simp)) v
  have hvalues := congrArg
    (fun L : SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n ↦ L v)
    (heq.mfderiv_eq (I := spacetimeModel n) (I' := spacetimeModel n))
  apply (boxTangentEquiv A b q).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hid : mfderiv (spacetimeModel n) (spacetimeModel n) (id : X → X) p v = v := by
    rw [mfderiv_id]
    rfl
  exact (hchain.symm.trans (hvalues.trans hid)).symm

theorem box_transition_mfderiv_apply (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (q : boxDomain (A.box b))
    (hq : (A.box b).toSpacetime q ∈ (boxHomeomorph (A.box c)).target)
    (v : SpacetimeModelVector n) :
    letI := intervalChartedSpace (A.box b).interval
    letI := intervalChartedSpace (A.box c).interval
    mfderiv (spacetimeModel n) (spacetimeModel n)
        ((boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime) q v =
      (boxTangentEquiv A c ((boxHomeomorph (A.box c)).symm ((A.box b).toSpacetime q))).symm
        (boxTangentEquiv A b q v) := by
  let := intervalChartedSpace (A.box b).interval
  let := intervalChartedSpace (A.box c).interval
  let := adaptedChartedSpace A
  have hinv := (box_inverse_smooth A c).contMDiffAt
    ((boxHomeomorph (A.box c)).open_target.mem_nhds hq)
  have hchain := mfderiv_comp_apply q (hinv.mdifferentiableAt (by simp))
    (((adapted_box_localDiffeomorph A b).contMDiff q).mdifferentiableAt (by simp)) v
  exact hchain.trans (box_inverse_mfderiv A c ((A.box b).toSpacetime q) hq
    (boxTangentEquiv A b q v)).symm

theorem boxHorizontalEquiv_transition (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (p : X) (hb : p ∈ (boxHomeomorph (A.box b)).target)
    (hc : p ∈ (boxHomeomorph (A.box c)).target) (v : EuclideanSpace ℝ (Fin n)) :
    letI := intervalChartedSpace (A.box b).interval
    letI := intervalChartedSpace (A.box c).interval
    (boxHorizontalEquiv A c p hc).symm (boxHorizontalEquiv A b p hb v) =
      (mfderiv (spacetimeModel n) (spacetimeModel n)
        ((boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime)
          ((boxHomeomorph (A.box b)).symm p) (0, v)).2 := by
  let := intervalChartedSpace (A.box b).interval
  let := intervalChartedSpace (A.box c).interval
  have hright := boxHomeomorph_right_inv (A.box b) hb
  have hq : (A.box b).toSpacetime ((boxHomeomorph (A.box b)).symm p) ∈
      (boxHomeomorph (A.box c)).target := hright.symm ▸ hc
  rw [boxHorizontalEquiv_symm_apply, boxHorizontalEquiv_apply,
    box_transition_mfderiv_apply A b c _ hq, hright]

end PoincareConjecture.Proofs.M11
