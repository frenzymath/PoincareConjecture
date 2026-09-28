import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.RealTime
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe v

namespace PoincareConjecture.Proofs.M15



theorem hasDerivWithinAt_comp_realParam
    {K : SpacetimeInterval}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : SmoothSpacetimeInterval K)
    {U : Set D.Point} (hU : IsOpen U) {f : D.Point → E}
    (hf : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, E) ∞ f U)
    (t : D.Point) (ht : t ∈ U) :
    HasDerivWithinAt (fun s => f (D.realParam s))
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, E) f t (D.positiveTangent t))
      K.domain t.val := by
  have hF : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, E) f (D.realParam t.val) := by
    simpa only [D.realParam_coe] using
      ((hf t ht).contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp)
  have hR : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ 1) D.realParam K.domain t.val :=
    D.realParam_smoothOn.mdifferentiableOn (by simp) t.val t.property
  have h := (hF.hasMFDerivAt.comp_hasMFDerivWithinAt t.val
    hR.hasMFDerivWithinAt).hasFDerivWithinAt.hasDerivWithinAt
  change HasDerivWithinAt (fun s => f (D.realParam s))
    (mfderiv (𝓡∂ 1) 𝓘(ℝ, E) f (D.realParam t.val)
      (mfderivWithin 𝓘(ℝ) (𝓡∂ 1) D.realParam K.domain t.val 1)) K.domain t.val at h
  rwa [D.realParam_mfderivWithin_one, D.realParam_coe] at h




theorem eq_of_mfderiv_positiveTangent_eq_zero_on_Icc
    {K : SpacetimeInterval}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : SmoothSpacetimeInterval K)
    {U : Set D.Point} (hU : IsOpen U) {f : D.Point → E}
    (hf : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, E) ∞ f U)
    (hz : ∀ t ∈ U, mfderiv (𝓡∂ 1) 𝓘(ℝ, E) f t
      (D.positiveTangent t) = 0)
    (a b : D.Point) (hab : a.val ≤ b.val)
    (hseg : ∀ t : D.Point, a.val ≤ t.val → t.val ≤ b.val → t ∈ U) :
    f a = f b := by
  have hsubset : Icc a.val b.val ⊆ K.domain := K.ordConnected.out a.property b.property
  have hd (s : ℝ) (hs : s ∈ Icc a.val b.val) :
      HasFDerivWithinAt (fun s => f (D.realParam s)) (0 : ℝ →L[ℝ] E)
        (Icc a.val b.val) s := by
    let t : D.Point := ⟨s, hsubset hs⟩
    have ht : t ∈ U := hseg t hs.1 hs.2
    have h := hasDerivWithinAt_comp_realParam D hU hf t ht
    rw [hz t ht] at h
    simpa using (h.mono hsubset).hasFDerivWithinAt
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0) hd
    (fun _ _ => by simp) (convex_Icc a.val b.val) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  have he : f (D.realParam b.val) - f (D.realParam a.val) = 0 :=
    norm_le_zero_iff.mp (by simpa only [zero_mul] using h)
  simpa only [D.realParam_coe] using (sub_eq_zero.mp he).symm

end PoincareConjecture.Proofs.M15
