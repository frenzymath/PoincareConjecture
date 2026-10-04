import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Spatial jets at time endpoints

Joint smoothness within a time set preserves the ordinary spatial jets
on an open spatial domain. This supplies endpoint continuity in
Morgan--Tian, Lemma 16.8 and Corollary 16.9, pp. 372-373.
See M44 derivation 34.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareMT.M44

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial differentiation uses the spatial restriction of the joint
within derivative, even at a time endpoint. Source: the fixed-coordinate
argument in Lemma 16.8, pp. 372-373; M44 derivation 34. -/
theorem spatial_fderiv_eq_fderivWithin {f : ℝ × V → E}
    {J : Set ℝ} {U : Set V} (hU : IsOpen U) {t : ℝ} (ht : t ∈ J)
    {x : V} (hx : x ∈ U) (hf : DifferentiableWithinAt ℝ f (J ×ˢ U) (t, x)) :
    fderiv ℝ (fun y => f (t, y)) x =
      (fderivWithin ℝ f (J ×ˢ U) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
  have hi : HasFDerivAt (fun y : V => (t, y)) (ContinuousLinearMap.inr ℝ ℝ V) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact ((hf.hasFDerivWithinAt.comp x hi.hasFDerivWithinAt
    (fun y hy => ⟨ht, hy⟩)).hasFDerivAt (hU.mem_nhds hx)).fderiv

/-- Ordinary spatial differentiation preserves smoothness on a product
with a uniquely differentiable time set. Source: Lemma 16.8, pp. 372-373;
M44 derivation 34. -/
theorem contDiffOn_spatialFDeriv_within {f : ℝ × V → E}
    {J : Set ℝ} {U : Set V} (hf : ContDiffOn ℝ ∞ f (J ×ˢ U))
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => fderiv ℝ (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  have hd := (hf.fderivWithin (hJ.prod hU.uniqueDiffOn) (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ V))
  apply hd.congr
  intro z hz
  exact spatial_fderiv_eq_fderivWithin hU hz.1 hz.2
    ((hf z hz).differentiableWithinAt (by simp))

/-- Every ordinary spatial jet is jointly smooth through the time
endpoints. Source: Corollary 16.9, p. 373; M44 derivation 34. -/
theorem contDiffOn_spatialJet_within {f : ℝ × V → E}
    {J : Set ℝ} {U : Set V} (hf : ContDiffOn ℝ ∞ f (J ×ˢ U))
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => iteratedFDeriv ℝ m (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  induction m with
  | zero =>
      let e := (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv
      exact e.toContinuousLinearMap.contDiff.comp_contDiffOn hf
  | succ m ih =>
      let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) E).symm
      convert! e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
        (contDiffOn_spatialFDeriv_within ih hJ hU) using 1

/-- Each spatial jet is smooth along its fixed time line within the
time set. Source: Corollary 16.9, p. 373; M44 derivation 34. -/
theorem contDiffOn_spatialJet_time_within {f : ℝ × V → E}
    {J : Set ℝ} {U : Set V} (hf : ContDiffOn ℝ ∞ f (J ×ˢ U))
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) (m : ℕ) {x : V} (hx : x ∈ U) :
    ContDiffOn ℝ ∞ (fun t => iteratedFDeriv ℝ m (fun y => f (t, y)) x) J :=
  (contDiffOn_spatialJet_within hf hJ hU m).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hx⟩)

end PoincareMT.M44
