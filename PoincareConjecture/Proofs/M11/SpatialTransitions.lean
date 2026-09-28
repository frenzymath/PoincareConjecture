import PoincareConjecture.Proofs.M11.BoxInverseDifferential





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def boxSpatialTransition (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (q : boxDomain (A.box b)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  letI := intervalChartedSpace (A.box b).interval
  letI := intervalChartedSpace (A.box c).interval
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin n))).comp
    ((mfderiv (spacetimeModel n) (spacetimeModel n)
      ((boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime) q).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin n))))

theorem boxSpatialTransition_eq (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (q : boxDomain (A.box b))
    (hq : (A.box b).toSpacetime q ∈ (boxHomeomorph (A.box c)).target)
    (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hψ : ContDiffAt ℝ ∞ ψ q.2.val)
    (heq : (fun r : boxDomain (A.box b) ↦
        ((boxHomeomorph (A.box c)).symm ((A.box b).toSpacetime r)).2.val) =ᶠ[𝓝 q]
      (fun r ↦ ψ r.2.val)) :
    boxSpatialTransition A b c q = fderiv ℝ ψ q.2.val := by
  let := intervalChartedSpace (A.box b).interval
  let := intervalChartedSpace (A.box c).interval
  let f : boxDomain (A.box b) → boxDomain (A.box c) :=
    (boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime
  have hf := (box_transition_smooth A b c).contMDiffAt
    (((boxHomeomorph (A.box b)).trans (boxHomeomorph (A.box c)).symm).open_source.mem_nhds
      ⟨mem_univ q, hq⟩)
  apply ContinuousLinearMap.ext
  intro v
  change (mfderiv (spacetimeModel n) (spacetimeModel n) f q (0, v)).2 = fderiv ℝ ψ q.2.val v
  have hchain := mfderiv_comp_apply q
    ((box_space_smooth (A.box c) (f q)).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp)) (0, v)
  rw [box_space_mfderiv] at hchain
  have hψchain := mfderiv_comp_apply q (hψ.contMDiffAt.mdifferentiableAt (by simp))
    ((box_space_smooth (A.box b) q).mdifferentiableAt (by simp)) (0, v)
  rw [box_space_mfderiv, mfderiv_eq_fderiv] at hψchain
  have hvalues := congrArg
    (fun L : SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L (0, v))
    (heq.mfderiv_eq (I := spacetimeModel n) (I' := 𝓡 n))
  exact hchain.symm.trans (hvalues.trans hψchain)

theorem boxSpatialTransition_smooth (A : AdaptedMetricAtlas n X) (b c : A.box_index) :
    ContMDiffOn (spacetimeModel n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (boxSpatialTransition A b c)
      ((boxHomeomorph (A.box b)).trans (boxHomeomorph (A.box c)).symm).source := by
  let := intervalChartedSpace (A.box b).interval
  let := intervalChartedSpace (A.box c).interval
  intro q hq
  obtain ⟨T⟩ := box_transition_data A b c q hq.2
  have hcoords := box_transition_eventually_eq (A.box b) (A.box c) q T
  have hT := (T.smooth.fderiv_of_isOpen T.coordinateChange.open_source
    (m := ∞) (by simp)).contDiffAt (T.coordinateChange.open_source.mem_nhds T.source_mem)
  have hlocal := hT.contMDiffAt.comp q (box_space_smooth (A.box b) q)
  apply ContMDiffAt.contMDiffWithinAt
  apply hlocal.congr_of_eventuallyEq
  have hsource : ∀ᶠ r : boxDomain (A.box b) in 𝓝 q,
      r.2.val ∈ T.coordinateChange.source :=
    ((box_space_smooth (A.box b) q).continuousAt.preimage_mem_nhds
      (T.coordinateChange.open_source.mem_nhds T.source_mem))
  filter_upwards [hcoords.eventually_nhds, hsource,
    ((boxHomeomorph (A.box b)).trans (boxHomeomorph (A.box c)).symm).open_source.mem_nhds hq]
    with r heq hr htarget
  exact boxSpatialTransition_eq A b c r htarget.2 T.coordinateChange
    (T.smooth.contDiffAt (T.coordinateChange.open_source.mem_nhds hr))
    (heq.mono fun _ h ↦ h.2)

end PoincareConjecture.Proofs.M11
