import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.RealTime










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in


theorem realParam_comp_mfderivWithin_one {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) {A : Set ℝ} {c : ℝ → ℝ} {s v : ℝ}
    (hs : s ∈ A) (hA : UniqueDiffWithinAt ℝ A s)
    (hc : HasDerivWithinAt c v A s) (hmap : MapsTo c A I.domain) :
    mfderivWithin (𝓘(ℝ, ℝ)) (𝓡∂ 1) (fun r => D.realParam (c r)) A s 1 =
      v • D.positiveTangent (D.realParam (c s)) := by
  have hd := mfderivWithin_comp s
    (D.realParam_smoothOn.mdifferentiableOn (by simp) _ (hmap hs))
    hc.hasFDerivWithinAt.hasMFDerivWithinAt.mdifferentiableWithinAt
    hmap hA.uniqueMDiffWithinAt
  rw [D.realParam_mfderivWithin (hmap hs), mfderivWithin_eq_fderivWithin,
    hc.hasFDerivWithinAt.fderivWithin hA] at hd
  have hv := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) => L 1) hd
  change mfderivWithin (𝓘(ℝ, ℝ)) (𝓡∂ 1) (fun r => D.realParam (c r)) A s 1 =
    v • (D.inclusionDerivative (D.realParam (c s))).symm 1
  calc
    _ = (D.inclusionDerivative (D.realParam (c s))).symm v := by
      convert! hv using 1
      change (D.inclusionDerivative (D.realParam (c s))).symm v =
        (D.inclusionDerivative (D.realParam (c s))).symm ((1 : ℝ) • v)
      rw [one_smul]
    _ = v • (D.inclusionDerivative (D.realParam (c s))).symm 1 := by
      simpa only [smul_eq_mul, mul_one] using
        (D.inclusionDerivative (D.realParam (c s))).symm.map_smul v (1 : ℝ)



theorem realParam_backward_contMDiffOn {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (T : ℝ) {A : Set ℝ}
    (hmap : MapsTo (fun s => T - s) A I.domain) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (fun s => D.realParam (T - s)) A :=
  D.realParam_smoothOn.comp (contDiff_const.sub contDiff_id).contMDiff.contMDiffOn hmap

set_option backward.isDefEq.respectTransparency false in


theorem realParam_backward_mfderiv_one {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (T : ℝ) {a b s : ℝ} (hs : s ∈ Ioo a b)
    (hmap : MapsTo (fun r => T - r) (Ioo a b) I.domain) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓡∂ 1) (fun r => D.realParam (T - r)) s 1 =
      -D.positiveTangent (D.realParam (T - s)) := by
  have hd : HasDerivWithinAt (fun r => T - r) (-1) (Ioo a b) s := by
    simpa using ((hasDerivAt_id s).const_sub T).hasDerivWithinAt
  have h := realParam_comp_mfderivWithin_one D hs
    (isOpen_Ioo.uniqueDiffWithinAt hs) hd hmap
  rw [mfderivWithin_eq_mfderiv (isOpen_Ioo.uniqueMDiffWithinAt hs)
    ((realParam_backward_contMDiffOn D T hmap).contMDiffAt
      (isOpen_Ioo.mem_nhds hs) |>.mdifferentiableAt (by simp))] at h
  simpa only [neg_one_smul] using h

end PoincareConjecture.M34
