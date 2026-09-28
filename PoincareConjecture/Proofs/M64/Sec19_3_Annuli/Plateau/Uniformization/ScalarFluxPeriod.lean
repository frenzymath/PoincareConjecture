import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugate
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology unitInterval

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

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

def scalarCirclePoint (r t : ℝ) : Plane :=
  (r * Real.cos (2 * Real.pi * t)) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
    (r * Real.sin (2 * Real.pi * t)) • EuclideanSpace.basisFun (Fin 2) ℝ 1

theorem scalarCirclePoint_norm (r t : ℝ) : ‖scalarCirclePoint r t‖ = |r| := by
  have hsq : ‖scalarCirclePoint r t‖ ^ 2 = r ^ 2 := by
    have heq : ‖scalarCirclePoint r t‖ ^ 2 =
        (r * Real.cos (2 * Real.pi * t)) ^ 2 + (r * Real.sin (2 * Real.pi * t)) ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, scalarCirclePoint]
    rw [heq, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp (by simpa only [sq_abs] using hsq)

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

def scalarFluxPeriod (H : Plane → ℝ) (r : ℝ) : ℝ :=
  curveIntegral (scalarConjugateForm D H) (scalarCirclePath r)

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

end PoincareConjecture.M64Uniformization
