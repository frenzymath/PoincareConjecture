import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeDiskMap
import PoincareConjecture.Proofs.M60.Mathlib.ConformalTrace
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

open Proofs.M58

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem m64LocalConeDiskMap_radial_column
    (H : ℝ × (M × M) → M) (center : M) (gamma : ℝ → M)
    (hperiod : Function.Periodic gamma curvePeriod) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 n)
      (m64LocalConeDiskMap H center gamma) (r • angularPoint t))
    (hH : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s => H (s, center, gamma t)) (1 - diskTimeProfile r)) :
    mfderiv (𝓡 2) (𝓡 n) (m64LocalConeDiskMap H center gamma)
        (r • angularPoint t) (angularPoint t) =
      -deriv diskTimeProfile r • mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (fun s => H (s, center, gamma t)) (1 - diskTimeProfile r) 1 := by
  let delta : ℝ → LoopPlane := fun s => s • angularPoint t
  have hd : HasDerivAt delta (angularPoint t) r := by
    simpa +instances only [one_smul] using! (hasDerivAt_id r).smul_const (angularPoint t)
  have hdv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) delta r 1 = angularPoint t := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hd.deriv
  let chi : ℝ → ℝ := fun s => 1 - diskTimeProfile s
  have hc : HasDerivAt chi (-deriv diskTimeProfile r) r := by
    simpa +instances only [zero_sub] using! (hasDerivAt_const r (1 : ℝ)).sub
      (contDiff_diskTimeProfile.differentiable (by simp) r).hasDerivAt
  have hcv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) chi r 1 = -deriv diskTimeProfile r := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hc.deriv
  have heq : (m64LocalConeDiskMap H center gamma ∘ delta) =ᶠ[𝓝 r]
      ((fun s => H (s, center, gamma t)) ∘ chi) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact m64LocalConeDiskMap_polar H center gamma hperiod hs t
  have he := congrArg (fun D => D (1 : ℝ))
    (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
  erw [mfderiv_comp_apply r hF hd.differentiableAt.mdifferentiableAt, hdv,
    mfderiv_comp_apply r hH hc.differentiableAt.mdifferentiableAt, hcv] at he
  apply he.trans
  simpa +instances only [smul_eq_mul, mul_one] using! (map_smul
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, center, gamma t))
      (1 - diskTimeProfile r)) (-deriv diskTimeProfile r) (1 : ℝ))

theorem m64LocalConeDiskMap_angular_column
    (H : ℝ × (M × M) → M) (center : M) (gamma : ℝ → M)
    (hperiod : Function.Periodic gamma curvePeriod) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma t)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 n)
      (m64LocalConeDiskMap H center gamma) (r • angularPoint t))
    (hH : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
      (1 - diskTimeProfile r, center, gamma t)) :
    mfderiv (𝓡 2) (𝓡 n) (m64LocalConeDiskMap H center gamma)
        (r • angularPoint t) (r • angularVector t) =
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
        (1 - diskTimeProfile r, center, gamma t) (0, 0, curveVelocity gamma t) := by
  let delta : ℝ → LoopPlane := fun s => r • angularPoint s
  have hd : HasDerivAt delta (r • angularVector t) t :=
    (hasDerivAt_angularPoint t).const_smul r
  have hdv : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) delta t 1 = r • angularVector t := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hd.deriv
  have hinput : MDifferentiableAt 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n)))
      (fun s => (1 - diskTimeProfile r, center, gamma s)) t :=
    mdifferentiableAt_const.prodMk (mdifferentiableAt_const.prodMk hgamma)
  have heq : m64LocalConeDiskMap H center gamma ∘ delta =
      (fun s => H (1 - diskTimeProfile r, center, gamma s)) :=
    funext (m64LocalConeDiskMap_polar H center gamma hperiod hr)
  have he := mfderiv_comp_apply t hF hd.differentiableAt.mdifferentiableAt (1 : ℝ)
  erw [heq, hdv] at he
  have hc := mfderiv_comp_apply_of_eq t hH hinput rfl (1 : ℝ)
  erw [mfderiv_prodMk mdifferentiableAt_const (mdifferentiableAt_const.prodMk hgamma),
    mfderiv_prodMk mdifferentiableAt_const hgamma] at hc
  simp only [mfderiv_const] at hc
  exact he.symm.trans hc

variable [IsManifold (𝓡 n) ∞ M]

theorem m64EnergyDensity_polar_frame (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) (t : ℝ) :
    m60EnergyDensity g f z =
      ((g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z (angularPoint t))) ^ 2 +
        (g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z (angularVector t))) ^ 2) / 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D := mfderiv (𝓡 2) (𝓡 n) f z
  let B : LinearMap.BilinForm ℝ LoopPlane :=
    (g.inner (f z)).toBilinForm.compl₁₂ D.toLinearMap D.toLinearMap
  let w : Fin 2 → LoopPlane := ![angularPoint t, angularVector t]
  have hw (i j : Fin 2) : inner ℝ (w i) (w j) =
      (1 : ℝ) * (if i = j then 1 else 0) := by
    fin_cases i <;> fin_cases j <;>
      simp only [PiLp.inner_apply, Fin.sum_univ_two] <;>
      norm_num [w, angularPoint, angularVector] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]
  have hh := M60.sum_bilinear_conformal_basis B (EuclideanSpace.basisFun (Fin 2) ℝ)
    w (by simp) zero_lt_one hw
  simp only [B, w, ContinuousLinearMap.toBilinForm_apply,
    LinearMap.compl₁₂_apply, Fin.sum_univ_two, ContinuousLinearMap.coe_coe,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hh
  have hinner (v : LoopPlane) : g.inner (f z) (D v) (D v) =
      (g.tangentNorm (f z) (D v)) ^ 2 := by
    change inner ℝ (D v) (D v) = ‖D v‖ ^ 2
    exact real_inner_self_eq_norm_sq _
  erw [hinner (angularPoint t), hinner (angularVector t)] at hh
  unfold m60EnergyDensity
  rw [Matrix.trace_fin_two]
  change (1 / 2 : ℝ) * (g.inner (f z) (D _) (D _) + g.inner (f z) (D _) (D _)) = _
  erw [← hh]
  ring

end PoincareConjecture
