import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.Conjugate
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# A genuine conserved annular flux period

The actual conjugate form is smooth and closed because its constructed
local primitives are smooth. An explicit radial homotopy between the
actual positively oriented circles stays in the annulus. The curve-integral
homotopy theorem then proves that their conjugate-form periods agree.
This proves conservation, not positivity, of the period.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology unitInterval

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- Smooth local primitives imply actual smoothness and closedness of the retained conjugate
form on the whole open annulus. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with
the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-flux-period.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarConjugateForm_smooth_closed {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) :
    ContDiffOn ℝ ∞ (scalarConjugateForm D H) scalarAnnulus ∧
      ∀ x ∈ scalarAnnulus, ∀ v w : Plane,
        fderiv ℝ (scalarConjugateForm D H) x v w =
          fderiv ℝ (scalarConjugateForm D H) x w v := by
  have hlocal (x : Plane) (hx : x ∈ scalarAnnulus) :
      ∃ V : Plane → ℝ, ContDiff ℝ ∞ V ∧
        fderiv ℝ V =ᶠ[𝓝 x] scalarConjugateForm D H := by
    obtain ⟨r, V, hr, -, hV, hdV⟩ := exists_local_annular_conjugate D hHs hlap hx
    refine ⟨V, hV, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    exact (hdV y hy).fderiv
  constructor
  · intro x hx
    obtain ⟨V, hV, heq⟩ := hlocal x hx
    exact (((hV.fderiv_right (m := ∞) (by simp)).contDiffAt).congr_of_eventuallyEq
      heq.symm).contDiffWithinAt
  · intro x hx v w
    obtain ⟨V, hV, heq⟩ := hlocal x hx
    rw [← heq.fderiv_eq]
    exact (hV.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)).eq v w

/-- The positively oriented circle parametrized over one unit interval. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-flux-period.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def scalarCirclePoint (r t : ℝ) : Plane :=
  (r * Real.cos (2 * Real.pi * t)) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
    (r * Real.sin (2 * Real.pi * t)) • EuclideanSpace.basisFun (Fin 2) ℝ 1

/-- The literal polar circle point has norm equal to the absolute radius, including zero and
negative radii. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project
construction in `proof-work/tasks/M64/derivations/2026-09-24-annular-flux-period.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarCirclePoint_norm (r t : ℝ) : ‖scalarCirclePoint r t‖ = |r| := by
  have hsq : ‖scalarCirclePoint r t‖ ^ 2 = r ^ 2 := by
    have heq : ‖scalarCirclePoint r t‖ ^ 2 =
        (r * Real.cos (2 * Real.pi * t)) ^ 2 + (r * Real.sin (2 * Real.pi * t)) ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, scalarCirclePoint]
    rw [heq, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp (by simpa only [sq_abs] using hsq)

/-- The actual closed curve used to measure the annular flux period. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-flux-period.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def scalarCirclePath (r : ℝ) :
    Path (r • EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (r • EuclideanSpace.basisFun (Fin 2) ℝ 0) where
  toFun t := scalarCirclePoint r t
  continuous_toFun := by unfold scalarCirclePoint; fun_prop
  source' := by simp [scalarCirclePoint]
  target' := by simp [scalarCirclePoint]

private def scalarCircleHomotopy (r s : ℝ) :
    (scalarCirclePath r : C(I, Plane)).Homotopy (scalarCirclePath s) where
  toFun z := scalarCirclePoint ((AffineMap.lineMap r s) (z.1 : ℝ)) z.2
  continuous_toFun := by unfold scalarCirclePoint; fun_prop
  map_zero_left := by intro t; simp [scalarCirclePath]
  map_one_left := by intro t; simp [scalarCirclePath]

/-- The literal curve integral of the actual retained conjugate form. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-flux-period.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def scalarFluxPeriod (H : Plane → ℝ) (r : ℝ) : ℝ :=
  curveIntegral (scalarConjugateForm D H) (scalarCirclePath r)

/-- The actual conjugate-form period is independent of the interior circle radius. The proof
constructs the radial homotopy and uses its smoothness and the proved closedness of the
actual one-form. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project
construction in `proof-work/tasks/M64/derivations/2026-09-24-annular-flux-period.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarFluxPeriod_eq {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    {r s : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) (hs : s ∈ Ioo (1 : ℝ) 2) :
    scalarFluxPeriod D H r = scalarFluxPeriod D H s := by
  obtain ⟨hωs, hclosed⟩ := scalarConjugateForm_smooth_closed D hHs hlap
  let φ := scalarCircleHomotopy r s
  have hrange : range φ ⊆ scalarAnnulus := by
    rintro y ⟨⟨a, b⟩, rfl⟩
    have hrad := (convex_Ioo (1 : ℝ) 2).lineMap_mem hr hs a.property
    change 1 < ‖scalarCirclePoint ((AffineMap.lineMap r s) (a : ℝ)) b‖ ∧
      ‖scalarCirclePoint ((AffineMap.lineMap r s) (a : ℝ)) b‖ < 2
    rw [scalarCirclePoint_norm, abs_of_pos (lt_trans zero_lt_one hrad.1)]
    exact hrad
  have hhom := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := range φ) («ω» := scalarConjugateForm D H)
    (dω := fderiv ℝ (scalarConjugateForm D H))
    (fun a _ b _ => mem_range_self (a, b))
    (fun x hx => ((hωs.contDiffAt (scalarAnnulus_isOpen.mem_nhds (hrange hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt) ?_ ?_ ?_
  · have hext : ((φ.evalAt 1).extend : ℝ → Plane) = ((φ.evalAt 0).extend : ℝ → Plane) := by
      change IccExtend zero_le_one (φ.evalAt 1) = IccExtend zero_le_one (φ.evalAt 0)
      congr 1
      funext t
      change scalarCirclePoint ((AffineMap.lineMap r s) (t : ℝ)) 1 =
        scalarCirclePoint ((AffineMap.lineMap r s) (t : ℝ)) 0
      simp [scalarCirclePoint]
    have hside : curveIntegral (scalarConjugateForm D H) (φ.evalAt 1) =
        curveIntegral (scalarConjugateForm D H) (φ.evalAt 0) := by
      simp only [curveIntegral_def, curveIntegralFun_def, hext]
    change scalarFluxPeriod D H r + _ = scalarFluxPeriod D H s + _ at hhom
    rw [hside] at hhom
    exact add_right_cancel hhom
  · rw [(isCompact_range φ.continuous).isClosed.closure_eq]
    exact hωs.continuousOn.mono hrange
  · intro x hx v _ w _
    exact hclosed x (hrange hx) v w
  · have heq : EqOn (fun z : ℝ × ℝ => IccExtend zero_le_one (φ.extend z.1) z.2)
        (fun z => scalarCirclePoint ((AffineMap.lineMap r s) z.1) z.2) (Icc 0 1) := by
      rw [Icc_prod_eq]
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      lift a to I using ha
      lift b to I using hb
      simp [φ, scalarCircleHomotopy]
      rfl
    exact .congr (by unfold scalarCirclePoint; fun_prop) heq

end PoincareMT.M64Uniformization
