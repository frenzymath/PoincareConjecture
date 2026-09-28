import PoincareConjecture.Definitions.Ch06.LGeometry
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Algebra.Structures









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J K : Set ℝ} {F : RicciFlow n M J} {G : RicciFlow n M K}
  {T U d sigma : ℝ}

omit [IsManifold (𝓡 n) ∞ M] in
private theorem normalized_curve_velocity {gamma : ℝ → M} {s : ℝ}
    (hgamma : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) gamma (d * s)) :
    curveVelocity (n := n) (fun r => gamma (d * r)) s =
      d • curveVelocity (n := n) gamma (d * s) := by
  have hd : HasDerivAt (fun r : ℝ => d * r) d s := by
    simpa using (hasDerivAt_id s).const_mul d
  have hvalue : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => d * r) s 1 = d := by
    rw [mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ d
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ => d * r) (g := gamma)
    hgamma hd.differentiableAt.mdifferentiableAt (1 : TangentSpace (𝓘(ℝ, ℝ)) s)
  have hinput : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => d * r) s 1 =
      d • (1 : TangentSpace (𝓘(ℝ, ℝ)) s) := by rw [hvalue]; simp
  rw [hinput, map_smul] at hchain
  change (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (gamma ∘ fun r : ℝ => d * r) s) 1 = _
  simpa only [curveVelocity, Function.comp_apply] using hchain

private theorem normalized_path_integrand (hd : 0 < d)
    (hmetric : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x (v w : TangentSpace (𝓡 n) x),
      (G.metric (U - s)).inner x v w = d⁻¹ * (F.metric (T - d * s)).inner x v w)
    (hscalar : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x,
      (G.connection (U - s)).scalarCurvature x =
        d * (F.connection (T - d * s)).scalarCurvature x)
    {gamma : ℝ → M} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) sigma)
    (hgamma : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) gamma (d * s)) :
    backwardLIntegrand G U (fun r => gamma (d * r)) s =
      Real.sqrt d * backwardLIntegrand F T gamma (d * s) := by
  rw [backwardLIntegrand, normalized_curve_velocity hgamma,
    hscalar s hs, hmetric s hs]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [backwardLIntegrand, Real.sqrt_mul hd.le]
  have hsqrt := Real.sq_sqrt hd.le
  field_simp
  rw [hsqrt]
  ring



noncomputable def seedNormalizedPath (hd : 0 < d) (hsigma : 0 < sigma)
    (hwindow : Icc (U - sigma) U ⊆ K)
    (hmetric : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x (v w : TangentSpace (𝓡 n) x),
      (G.metric (U - s)).inner x v w = d⁻¹ * (F.metric (T - d * s)).inner x v w)
    (hscalar : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x,
      (G.connection (U - s)).scalarCurvature x =
        d * (F.connection (T - d * s)).scalarCurvature x)
    (p : BackwardTimePath F T 0 (d * sigma)) : BackwardTimePath G U 0 sigma where
  curve := fun s => p.curve (d * s)
  nonnegative := le_rfl
  ordered := hsigma
  terminal_mem := hwindow ⟨by linarith, le_rfl⟩
  time_mem := fun s hs => hwindow ⟨by linarith [hs.2], by linarith [hs.1]⟩
  continuous := p.continuous.comp (continuous_const.mul continuous_id).continuousOn
    (fun s hs => ⟨mul_nonneg hd.le hs.1, mul_le_mul_of_nonneg_left hs.2 hd.le⟩)
  regular := p.regular.comp (contMDiff_const.mul contMDiff_id).contMDiffOn
    (fun s hs => ⟨mul_pos hd hs.1, mul_lt_mul_of_pos_left hs.2 hd⟩)
  l_integrable := by
    have hi := (p.l_integrable.comp_mul_left (c := d)).const_mul (Real.sqrt d)
    simp only [zero_div, mul_div_cancel_left₀ sigma hd.ne'] at hi
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le hsigma.le] at hs
    have hs' : d * s ∈ Ioo (0 : ℝ) (d * sigma) :=
      ⟨mul_pos hd hs.1, mul_lt_mul_of_pos_left hs.2 hd⟩
    exact (normalized_path_integrand hd hmetric hscalar ⟨hs.1.le, hs.2.le⟩
      ((p.regular.contMDiffAt (isOpen_Ioo.mem_nhds hs')).mdifferentiableAt one_ne_zero)).symm


theorem seedNormalizedPath_length (hd : 0 < d) (hsigma : 0 < sigma)
    (hwindow : Icc (U - sigma) U ⊆ K)
    (hmetric : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x (v w : TangentSpace (𝓡 n) x),
      (G.metric (U - s)).inner x v w = d⁻¹ * (F.metric (T - d * s)).inner x v w)
    (hscalar : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x,
      (G.connection (U - s)).scalarCurvature x =
        d * (F.connection (T - d * s)).scalarCurvature x)
    (p : BackwardTimePath F T 0 (d * sigma)) :
    backwardLLength G U 0 sigma
        (seedNormalizedPath hd hsigma hwindow hmetric hscalar p).curve =
      backwardLLength F T 0 (d * sigma) p.curve / Real.sqrt d := by
  change (∫ s in 0..sigma, backwardLIntegrand G U (fun r => p.curve (d * r)) s) = _
  have heq : (∫ s in 0..sigma, backwardLIntegrand G U (fun r => p.curve (d * r)) s) =
      ∫ s in 0..sigma, Real.sqrt d * backwardLIntegrand F T p.curve (d * s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hsigma.le
    intro s hs
    have hs' : d * s ∈ Ioo (0 : ℝ) (d * sigma) :=
      ⟨mul_pos hd hs.1, mul_lt_mul_of_pos_left hs.2 hd⟩
    exact normalized_path_integrand hd hmetric hscalar ⟨hs.1.le, hs.2.le⟩
      ((p.regular.contMDiffAt (isOpen_Ioo.mem_nhds hs')).mdifferentiableAt one_ne_zero)
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ hd.ne', mul_zero]
  change Real.sqrt d * (d⁻¹ * backwardLLength F T 0 (d * sigma) p.curve) = _
  have hsqrt := Real.sq_sqrt hd.le
  have hpos := Real.sqrt_pos.mpr hd
  field_simp
  rw [hsqrt]

end PoincareConjecture.Proofs.M47
