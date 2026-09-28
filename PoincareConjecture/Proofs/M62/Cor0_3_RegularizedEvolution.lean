import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem regularized_arcSecond_identity
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {ε t : ℝ}
    (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x =
      2 * (m62ArcDerivative F c t (m62RegularizedCurvature F c ε t) x) ^ 2 +
      2 * m62RegularizedCurvature F c ε t x *
        m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x := by
  let h := m62RegularizedCurvature F c ε t
  have hh : ContDiff ℝ ∞ h :=
    (regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hL : ContDiff ℝ ∞ (m62ArcDerivative F c t h) :=
    (hv.inv (fun y => (speed_pos F c hc (Set.Ioo_subset_Icc_self ht) y).ne')).mul
      (contDiff_infty_iff_deriv.mp hh).2
  have hq (y : ℝ) : HasDerivAt (m62CurvatureSquared F c t)
      (2 * h y * deriv h y) y := by
    have hd := (((hh.differentiable (by simp)) y).hasDerivAt.pow 2).sub_const (ε ^ 2)
    convert! hd using 1
    · funext z
      change m62CurvatureSquared F c t z =
        m62RegularizedCurvature F c ε t z ^ 2 - ε ^ 2
      rw [regularized_sq F c ε t z]
      ring
    · ring
  have harc : m62ArcDerivative F c t (m62CurvatureSquared F c t) =
      fun y => 2 * h y * m62ArcDerivative F c t h y := by
    funext y
    dsimp only [m62ArcDerivative]
    rw [(hq y).deriv]
    ring
  have hd : deriv (fun y => 2 * h y * m62ArcDerivative F c t h y) x =
      2 * deriv h x * m62ArcDerivative F c t h x +
        2 * h x * deriv (m62ArcDerivative F c t h) x :=
    ((((hh.differentiable (by simp)) x).hasDerivAt.const_mul 2).mul
      ((hL.differentiable (by simp)) x).hasDerivAt).deriv
  unfold m62ArcSecondDerivative
  rw [harc]
  change (curveSpeed F c t x)⁻¹ *
      deriv (fun y => 2 * h y * m62ArcDerivative F c t h y) x =
    2 * (m62ArcDerivative F c t h x) ^ 2 +
      2 * h x * ((curveSpeed F c t x)⁻¹ * deriv (m62ArcDerivative F c t h) x)
  rw [hd]
  dsimp only [m62ArcDerivative]
  ring




theorem regularized_deriv_le [T2Space M]
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    deriv (fun s => m62RegularizedCurvature F c ε s x) t ≤
      m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x +
        (m62Curvature F c t x) ^ 3 +
        m62C1 K0 K1 K2 * (m62RegularizedCurvature F c ε t x + 1) := by
  let h := m62RegularizedCurvature F c ε t x
  let k := m62Curvature F c t x
  let q := m62CurvatureSquared F c t x
  have hh : 0 < h := regularized_pos F c hε t x
  have hk : 0 ≤ k := curvature_nonneg F c t x
  have hkq : k ^ 2 = q := curvature_sq F c t x
  have hkh : k ≤ h := curvature_le_regularized F c ε t x
  have hsq : h ^ 2 = q + ε ^ 2 := regularized_sq F c ε t x
  have hquartic : q ^ 2 ≤ h * k ^ 3 := by
    calc
      q ^ 2 = k ^ 4 := by rw [← hkq]; ring
      _ ≤ h * k ^ 3 := by
        convert! mul_le_mul_of_nonneg_right hkh (pow_nonneg hk 3) using 1
        ring
  have hsum : q + k ≤ h * (h + 1) := by
    nlinarith only [hkh, hsq, sq_nonneg ε]
  have hC : 0 ≤ m62C0 K0 K1 K2 := by
    dsimp only [m62C0]
    positivity
  have herror := mul_le_mul_of_nonneg_left hsum hC
  have hgrad := regularized_gradient_le F c hc hε ht x
  have hbound := spatial_squared_bound F c hc h0 h1 h2 hBounds ht x
  rw [(hasDerivAt_curvatureSquared F c hc ht x).deriv,
    regularized_arcSecond_identity F c hc hε ht x] at hbound
  rw [(regularized_hasDerivAt_time F c hε
    (hasDerivAt_curvatureSquared F c hc ht x)).deriv]
  apply (div_le_iff₀ (mul_pos (by norm_num) hh)).mpr
  dsimp only [m62C1]
  nlinarith only [hbound, hgrad, hquartic, herror]

end PoincareConjecture.M62
