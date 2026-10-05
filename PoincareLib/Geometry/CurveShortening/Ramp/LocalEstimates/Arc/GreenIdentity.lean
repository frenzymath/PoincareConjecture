import PoincareLib.Geometry.CurveShortening.Ramp.LocalEstimates.Fixed.ArcLength
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Green identity for the actual scalar arc operator

The witnessed derivative of the boundary flux gives integration by parts
against the actual speed. Both boundary values and first arc derivatives
are retained. MT2007 Claim 19.61, pp. 484-485;
`2026-09-22-uniform-estimate-arc-green-identity.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

/-- The actual scalar second arc operator has its exact Green boundary
flux on any oriented parameter interval. MT2007 Claim 19.61, pp. 484-485;
the actual speed normalization is differentiated in full. -/
theorem m63ArcSecond_green_identity (hc : M62ShrinkingCurve F c)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (phi h : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hh : ContDiff ℝ 2 h) (alpha beta : ℝ) :
    (∫ x in alpha..beta,
      (phi x * m62ArcSecondDerivative F c t h x -
        h x * m62ArcSecondDerivative F c t phi x) * curveSpeed F c t x) =
      (phi beta * m62ArcDerivative F c t h beta -
        h beta * m62ArcDerivative F c t phi beta) -
      (phi alpha * m62ArcDerivative F c t h alpha -
        h alpha * m62ArcDerivative F c t phi alpha) := by
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hpos (x : ℝ) : 0 < curveSpeed F c t x :=
    speed_pos F c hc (Set.Ioo_subset_Icc_self ht) x
  have hfirst {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
      ContDiff ℝ 1 (m62ArcDerivative F c t f) :=
    ((hv.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).inv (fun x => (hpos x).ne')).mul
      hf.deriv'
  have hsecond {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
      Continuous (m62ArcSecondDerivative F c t f) :=
    (hv.continuous.inv₀ (fun x => (hpos x).ne')).mul
      (hfirst hf).continuous_deriv_one
  let W := fun x => phi x * m62ArcDerivative F c t h x -
    h x * m62ArcDerivative F c t phi x
  have hW (x : ℝ) : HasDerivAt W
      ((phi x * m62ArcSecondDerivative F c t h x -
        h x * m62ArcSecondDerivative F c t phi x) * curveSpeed F c t x) x := by
    have hphi' := ((hphi.differentiable (by norm_num)) x).hasDerivAt
    have hh' := ((hh.differentiable (by norm_num)) x).hasDerivAt
    have hDphi := (((hfirst hphi).differentiable (by norm_num)) x).hasDerivAt
    have hDh := (((hfirst hh).differentiable (by norm_num)) x).hasDerivAt
    apply ((hphi'.mul hDh).sub (hh'.mul hDphi)).congr_deriv
    dsimp only [m62ArcSecondDerivative, m62ArcDerivative]
    field_simp [(hpos x).ne']
    ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hW x)
    ((((hphi.continuous.mul (hsecond hh)).sub
      (hh.continuous.mul (hsecond hphi))).mul hv.continuous).intervalIntegrable alpha beta)

/-- Vanishing cutoff values and first arc derivatives remove both Green
boundary terms. MT2007 Claim 19.61, pp. 484-485. The four actual endpoint
guards are separate; no sign or ordering premise is needed. -/
theorem m63ArcSecond_integral_transfer (hc : M62ShrinkingCurve F c)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (phi h : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hh : ContDiff ℝ 2 h) (alpha beta : ℝ)
    (hphiA : phi alpha = 0) (hphiB : phi beta = 0)
    (hDA : m62ArcDerivative F c t phi alpha = 0)
    (hDB : m62ArcDerivative F c t phi beta = 0) :
    (∫ x in alpha..beta,
      phi x * m62ArcSecondDerivative F c t h x * curveSpeed F c t x) =
      ∫ x in alpha..beta,
        h x * m62ArcSecondDerivative F c t phi x * curveSpeed F c t x := by
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hpos (x : ℝ) : 0 < curveSpeed F c t x :=
    speed_pos F c hc (Set.Ioo_subset_Icc_self ht) x
  have hfirst {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
      ContDiff ℝ 1 (m62ArcDerivative F c t f) :=
    ((hv.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).inv (fun x => (hpos x).ne')).mul
      hf.deriv'
  have hsecond {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
      Continuous (m62ArcSecondDerivative F c t f) :=
    (hv.continuous.inv₀ (fun x => (hpos x).ne')).mul
      (hfirst hf).continuous_deriv_one
  have hleft : IntervalIntegrable (fun x =>
      phi x * m62ArcSecondDerivative F c t h x * curveSpeed F c t x)
      MeasureTheory.volume alpha beta :=
    ((hphi.continuous.mul (hsecond hh)).mul hv.continuous).intervalIntegrable alpha beta
  have hright : IntervalIntegrable (fun x =>
      h x * m62ArcSecondDerivative F c t phi x * curveSpeed F c t x)
      MeasureTheory.volume alpha beta :=
    ((hh.continuous.mul (hsecond hphi)).mul hv.continuous).intervalIntegrable alpha beta
  have hgreen := m63ArcSecond_green_identity F c hc ht phi h hphi hh alpha beta
  simp only [hphiA, hphiB, hDA, hDB, zero_mul, mul_zero, sub_zero] at hgreen
  simp_rw [sub_mul] at hgreen
  rw [intervalIntegral.integral_sub hleft hright] at hgreen
  exact sub_eq_zero.mp hgreen

end PoincareMT
