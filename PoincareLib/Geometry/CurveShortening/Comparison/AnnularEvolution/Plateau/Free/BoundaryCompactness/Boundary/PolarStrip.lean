import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.Strip
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.SeamGeometry

/-! Actual logarithmic upper-semicircle strips centered at a radial
boundary point. The half-angle parametrization uses the original full
rectangle and has Jacobian equal to half the squared radius.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain

/-- The actual logarithmic upper-semicircle parametrization using the half-angle coordinate.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
def boundaryPolarStrip (x rho : ℝ) (p : LoopPlane) : LoopPlane :=
  annulusPoint x 0 + (rho * Real.exp (-p 1)) • angularPoint (p 0 / 2)

/-- The upper-semicircle strip parametrization is smooth. Source: Morgan-Tian Lemma 19.15,
pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem boundaryPolarStrip_contDiff (x rho : ℝ) :
    ContDiff ℝ ∞ (boundaryPolarStrip x rho) := by
  have h0 : ContDiff ℝ ∞ (fun p : LoopPlane => p 0) := by fun_prop
  have h1 : ContDiff ℝ ∞ (fun p : LoopPlane => p 1) := by fun_prop
  exact contDiff_const.add ((contDiff_const.mul h1.neg.exp).smul
    (contDiff_angularPoint.comp (h0.div_const 2)))

/-- The actual upper-semicircle strip derivative has its stated radial and angular columns.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem boundaryPolarStrip_fderiv (x rho : ℝ) (p v : LoopPlane) :
    fderiv ℝ (boundaryPolarStrip x rho) p v =
      (-v 1 * (rho * Real.exp (-p 1))) • angularPoint (p 0 / 2) +
        (v 0 / 2 * (rho * Real.exp (-p 1))) • angularVector (p 0 / 2) := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have hr := h1.neg.exp.const_mul rho
  have hhalf : HasFDerivAt (fun q : LoopPlane => q 0 / 2)
      ((1 / 2 : ℝ) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) p := by
    simpa [div_eq_mul_inv, mul_comm] using h0.const_mul (1 / 2 : ℝ)
  have ht := (hasDerivAt_angularPoint (p 0 / 2)).hasFDerivAt.comp p hhalf
  have hh := (hasFDerivAt_const (annulusPoint x 0) p).add (hr.smul ht)
  change HasFDerivAt (boundaryPolarStrip x rho) _ p at hh
  rw [hh.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, neg_apply,
    EuclideanSpace.coe_proj, Function.comp_apply, Pi.neg_apply, smul_smul, zero_add]
  module

/-- The upper-semicircle Jacobian is half the squared radius. Source: Morgan-Tian Lemma
19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem boundaryPolarStrip_det (x rho : ℝ) (p : LoopPlane) :
    (fderiv ℝ (boundaryPolarStrip x rho) p).det = (rho * Real.exp (-p 1)) ^ 2 / 2 := by
  change LinearMap.det (fderiv ℝ (boundaryPolarStrip x rho) p).toLinearMap = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    ContinuousLinearMap.coe_coe]
  change (fderiv ℝ (boundaryPolarStrip x rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 0 *
      (fderiv ℝ (boundaryPolarStrip x rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 1 -
    (fderiv ℝ (boundaryPolarStrip x rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 0 *
      (fderiv ℝ (boundaryPolarStrip x rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 1 = _
  simp only [boundaryPolarStrip_fderiv]
  simp [EuclideanSpace.basisFun_apply, angularPoint, angularVector]
  nlinarith [congrArg (fun t : ℝ => (rho * Real.exp (-p 1)) ^ 2 * t)
    (Real.sin_sq_add_cos_sq (p 0 / 2))]

/-- The upper-semicircle strip is injective on the actual open rectangle. Source:
Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem boundaryPolarStrip_injOn (x : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    InjOn (boundaryPolarStrip x rho) S := by
  intro p hp q hq heq
  have hp' := (m64AnnulusInterior_coordinates p).mp hp
  have hq' := (m64AnnulusInterior_coordinates q).mp hq
  have hpT : (rho * Real.exp (-p 1), p 0 / 2) ∈ polarCoord.target := by
    change 0 < rho * Real.exp (-p 1) ∧ -Real.pi < p 0 / 2 ∧ p 0 / 2 < Real.pi
    unfold curvePeriod at hp'
    exact ⟨by positivity, by linarith [Real.pi_pos], by linarith⟩
  have hqT : (rho * Real.exp (-q 1), q 0 / 2) ∈ polarCoord.target := by
    change 0 < rho * Real.exp (-q 1) ∧ -Real.pi < q 0 / 2 ∧ q 0 / 2 < Real.pi
    unfold curvePeriod at hq'
    exact ⟨by positivity, by linarith [Real.pi_pos], by linarith⟩
  have hpol : polarCoord.symm (rho * Real.exp (-p 1), p 0 / 2) =
      polarCoord.symm (rho * Real.exp (-q 1), q 0 / 2) := by
    apply loopPlaneEquivProd.symm.injective
    rw [loopPlaneEquivProd_symm_polar, loopPlaneEquivProd_symm_polar]
    exact add_left_cancel heq
  have hpq := polarCoord.symm.injOn hpT hqT hpol
  have hangle := congrArg Prod.snd hpq
  have hr := mul_left_cancel₀ hrho.ne' (congrArg Prod.fst hpq)
  have hheight := neg_injective (Real.exp_injective hr)
  ext i
  fin_cases i
  · change p 0 / 2 = q 0 / 2 at hangle
    change p 0 = q 0
    linarith
  · exact hheight

/-- The upper logarithmic shell adjacent to a radial boundary. Source: Morgan-Tian Lemma
19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
def upperBoundaryShell (x rho : ℝ) : Set LoopPlane :=
  (Metric.closedBall (annulusPoint x 0) rho \
    Metric.closedBall (annulusPoint x 0) (rho * Real.exp (-1))) ∩ {p | 0 < p 1}

/-- The actual upper logarithmic shell is measurable. Source: Morgan-Tian Lemma 19.15, pp.
447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem upperBoundaryShell_measurable (x rho : ℝ) : MeasurableSet (upperBoundaryShell x rho) := by
  exact (measurableSet_closedBall.diff measurableSet_closedBall).inter
    (measurableSet_lt measurable_const (by fun_prop))

/-- The actual upper-semicircle strip maps into its logarithmic shell. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem boundaryPolarStrip_mapsTo_shell (x : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    MapsTo (boundaryPolarStrip x rho) S (upperBoundaryShell x rho) := by
  intro p hp
  have hc := (m64AnnulusInterior_coordinates p).mp hp
  have hdist : dist (boundaryPolarStrip x rho p) (annulusPoint x 0) =
      rho * Real.exp (-p 1) := by
    rw [dist_eq_norm]
    change ‖annulusPoint x 0 + (rho * Real.exp (-p 1)) • angularPoint (p 0 / 2) -
      annulusPoint x 0‖ = _
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity),
      norm_angularPoint, mul_one]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, hdist]
    exact mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by linarith [hc.2.2.1]))
  · rw [Metric.mem_closedBall, hdist, not_le]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith [hc.2.2.2])) hrho
  · change 0 < 0 + (rho * Real.exp (-p 1)) * Real.sin (p 0 / 2)
    have hangle : p 0 / 2 ∈ Ioo (0 : ℝ) Real.pi := by
      unfold curvePeriod at hc
      constructor <;> linarith
    simpa only [zero_add] using mul_pos (by positivity : 0 < rho * Real.exp (-p 1))
      (Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2)

/-- A sufficiently small upper logarithmic shell lies in the annular interior. Source:
Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem upperBoundaryShell_subset_interior {x rho : ℝ}
    (hx : rho < x) (hP : x + rho < curvePeriod) (hr : rho < 1) :
    upperBoundaryShell x rho ⊆ S := by
  intro p hp
  have hd := Metric.mem_closedBall.mp hp.1.1
  rw [dist_eq_norm] at hd
  have h0 := (PiLp.norm_apply_le (p - annulusPoint x 0) 0).trans hd
  have h1 := (PiLp.norm_apply_le (p - annulusPoint x 0) 1).trans hd
  change ‖p 0 - x‖ ≤ rho at h0
  change ‖p 1 - 0‖ ≤ rho at h1
  rw [Real.norm_eq_abs] at h0 h1
  apply (m64AnnulusInterior_coordinates p).mpr
  have ha0 := (abs_le.mp h0)
  have ha1 := (abs_le.mp h1)
  exact ⟨by linarith [ha0.1], by linarith [ha0.2], hp.2, by linarith [ha1.2]⟩

end PoincareMT.M64
