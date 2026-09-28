import PoincareConjecture.Proofs.M11.BoxDifferential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def adaptedTimeVector (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    ∀ p : X, TangentSpace (spacetimeModel n) p := by
  letI := adaptedChartedSpace A
  intro p
  let b := Classical.choose (box_targets_cover A p)
  letI := intervalChartedSpace (A.box b).interval
  let q := (boxHomeomorph (A.box b)).symm p
  exact mfderiv (spacetimeModel n) (spacetimeModel n) (A.box b).toSpacetime q
    (boxPositiveTangent (A.box b) q)

theorem adaptedTimeVector_box (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (p : boxDomain (A.box b)) :
    letI := intervalChartedSpace (A.box b).interval
    letI := adaptedChartedSpace A
    adaptedTimeVector A ((A.box b).toSpacetime p) =
      mfderiv (spacetimeModel n) (spacetimeModel n) (A.box b).toSpacetime p
        (boxPositiveTangent (A.box b) p) := by
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  let c := Classical.choose (box_targets_cover A ((A.box b).toSpacetime p))
  let := intervalChartedSpace (A.box c).interval
  let f : boxDomain (A.box b) → boxDomain (A.box c) :=
    (boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime
  have hp : (A.box b).toSpacetime p ∈ (boxHomeomorph (A.box c)).target :=
    Classical.choose_spec (box_targets_cover A ((A.box b).toSpacetime p))
  have hf : ContMDiffAt (spacetimeModel n) (spacetimeModel n) ∞ f p :=
    (box_transition_smooth A b c).contMDiffAt
      (((boxHomeomorph (A.box b)).trans (boxHomeomorph (A.box c)).symm).open_source.mem_nhds
        ⟨mem_univ p, hp⟩)
  have heq : (A.box c).toSpacetime ∘ f =ᶠ[𝓝 p] (A.box b).toSpacetime := by
    filter_upwards [((boxHomeomorph (A.box c)).open_target.preimage
      (A.box b).openEmbedding.continuous).mem_nhds hp] with q hq
    exact boxHomeomorph_right_inv (A.box c) hq
  have hchain := mfderiv_comp_apply p
    (((adapted_box_localDiffeomorph A c).contMDiff (f p)).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp)) (boxPositiveTangent (A.box b) p)
  have hvalues := congrArg
    (fun L : SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n ↦
      L (boxPositiveTangent (A.box b) p))
    (heq.mfderiv_eq (I := spacetimeModel n) (I' := spacetimeModel n))
  have hvector := box_transition_positive A b c p hp
  rw [hvector] at hchain
  exact hchain.symm.trans hvalues

theorem adaptedTimeVector_normalized (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    ∀ p : X, mfderiv (spacetimeModel n) 𝓘(ℝ) A.time p (adaptedTimeVector A p) = 1 := by
  let := adaptedChartedSpace A
  intro p
  let b := Classical.choose (box_targets_cover A p)
  let := intervalChartedSpace (A.box b).interval
  let q := (boxHomeomorph (A.box b)).symm p
  have hp : p ∈ (boxHomeomorph (A.box b)).target :=
    Classical.choose_spec (box_targets_cover A p)
  have hright : (A.box b).toSpacetime q = p := boxHomeomorph_right_inv (A.box b) hp
  have hchain := mfderiv_comp_apply q
    ((adapted_time_smooth A ((A.box b).toSpacetime q)).mdifferentiableAt (by simp))
    (((adapted_box_localDiffeomorph A b).contMDiff q).mdifferentiableAt (by simp))
    (boxPositiveTangent (A.box b) q)
  have heq : A.time ∘ (A.box b).toSpacetime = (fun q : boxDomain (A.box b) ↦ q.1.val) :=
    funext (A.box b).time_toSpacetime
  rw [heq, boxPositiveTangent_normalized, hright] at hchain
  exact hchain.symm

theorem adaptedTimeVector_smooth (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun p : X ↦ Bundle.TotalSpace.mk' (SpacetimeModelVector n)
        (E := (TangentSpace (spacetimeModel n) : X → Type _)) p (adaptedTimeVector A p)) := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  apply (cover_smooth_iff (fun b ↦ boxHomeomorph (A.box b)) (box_targets_cover A)
    (box_transition_smooth A) _).mpr
  intro b
  let := intervalChartedSpace (A.box b).interval
  let : IsManifold (𝓡∂ 1) ∞ (A.box b).interval.domain := interval_isManifold (A.box b).interval
  have hmap := (adapted_box_localDiffeomorph A b).contMDiff.contMDiff_tangentMap
    (m := ∞) (by simp)
  have hcomp := hmap.comp (boxPositiveTangent_smooth (A.box b))
  apply hcomp.contMDiffOn.congr
  intro q _
  change Bundle.TotalSpace.mk' (SpacetimeModelVector n) ((A.box b).toSpacetime q)
      (adaptedTimeVector A ((A.box b).toSpacetime q)) =
    Bundle.TotalSpace.mk' (SpacetimeModelVector n) ((A.box b).toSpacetime q)
      (mfderiv (spacetimeModel n) (spacetimeModel n) (A.box b).toSpacetime q
        (boxPositiveTangent (A.box b) q))
  rw [adaptedTimeVector_box]

end PoincareConjecture.Proofs.M11
