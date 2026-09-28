import PoincareConjecture.Proofs.M11.BoxVector





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem box_transition_positive (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (p : boxDomain (A.box b))
    (hp : (A.box b).toSpacetime p ∈ (boxHomeomorph (A.box c)).target) :
    let f : boxDomain (A.box b) → boxDomain (A.box c) :=
      (boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime
    mfderiv (spacetimeModel n) (spacetimeModel n) f p (boxPositiveTangent (A.box b) p) =
      boxPositiveTangent (A.box c) (f p) := by
  let := intervalChartedSpace (A.box b).interval
  let := intervalChartedSpace (A.box c).interval
  let f : boxDomain (A.box b) → boxDomain (A.box c) :=
    (boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime
  let v := boxPositiveTangent (A.box b) p
  have hf : ContMDiffAt (spacetimeModel n) (spacetimeModel n) ∞ f p :=
    (box_transition_smooth A b c).contMDiffAt
      (((boxHomeomorph (A.box b)).trans (boxHomeomorph (A.box c)).symm).open_source.mem_nhds
        ⟨mem_univ p, hp⟩)
  obtain ⟨T⟩ := box_transition_data A b c p hp
  have hcoords := box_transition_eventually_eq (A.box b) (A.box c) p T
  apply Prod.ext
  · apply ((smoothInterval (A.box c).interval).inclusionDerivative (f p).1).injective
    have heq : (fun q : boxDomain (A.box b) ↦ (f q).1.val) =ᶠ[𝓝 p]
        (fun q ↦ q.1.val) := hcoords.mono fun _ h ↦ h.1
    have hnorm : mfderiv (spacetimeModel n) 𝓘(ℝ)
        ((fun q : boxDomain (A.box c) ↦ q.1.val) ∘ f) p v = 1 := by
      exact (congrArg (fun L : SpacetimeModelVector n →L[ℝ] ℝ ↦ L v)
        (heq.mfderiv_eq (I := spacetimeModel n) (I' := 𝓘(ℝ)))).trans
          (boxPositiveTangent_normalized (A.box b) p)
    have hchain := mfderiv_comp_apply p
      ((box_time_smooth (A.box c) (f p)).mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp)) v
    rw [box_time_mfderiv] at hchain
    exact (hchain.symm.trans hnorm).trans
      (((smoothInterval (A.box c).interval).inclusionDerivative (f p).1).apply_symm_apply 1).symm
  · have heq : (fun q : boxDomain (A.box b) ↦ (f q).2.val) =ᶠ[𝓝 p]
        (fun q ↦ T.coordinateChange q.2.val) := hcoords.mono fun _ h ↦ h.2
    have hT : MDifferentiableAt (𝓡 n) (𝓡 n) T.coordinateChange p.2.val :=
      (T.smooth.contDiffAt (T.coordinateChange.open_source.mem_nhds T.source_mem)).contMDiffAt
        |>.mdifferentiableAt (by simp)
    have hzero : mfderiv (spacetimeModel n) (𝓡 n)
        ((fun q : boxDomain (A.box c) ↦ q.2.val) ∘ f) p v = 0 := by
      apply (congrArg
        (fun L : SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L v)
        (heq.mfderiv_eq (I := spacetimeModel n) (I' := 𝓡 n))).trans
      change mfderiv (spacetimeModel n) (𝓡 n)
        (T.coordinateChange ∘ (fun q : boxDomain (A.box b) ↦ q.2.val)) p v = 0
      rw [mfderiv_comp_apply p hT
        ((box_space_smooth (A.box b) p).mdifferentiableAt (by simp)), box_space_mfderiv]
      exact map_zero _
    have hchain := mfderiv_comp_apply p
      ((box_space_smooth (A.box c) (f p)).mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp)) v
    rw [box_space_mfderiv] at hchain
    exact hchain.symm.trans hzero

end PoincareConjecture.Proofs.M11
