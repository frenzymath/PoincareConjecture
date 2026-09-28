import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem fderiv2_parametrization_le_of_hessian_le (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ e.source)
    {f : M → ℝ} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e z))
    (hgrad : g.inner (e z) (D.gradient f (e z)) (D.gradient f (e z)) = 1)
    {H A G : ℝ} (hH : 0 ≤ H) (hA : 1 ≤ A) (_hG : 0 ≤ G)
    (hmetric : ∀ v : EuclideanSpace ℝ (Fin n),
      g.pullbackCoefficients e z v v ≤ A * ‖v‖ ^ 2)
    (hchristoffel : ‖CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients e) z‖ ≤ G)
    (hhess : ∀ w : TangentSpace (𝓡 n) (e z),
      D.hessian f (e z) w w ≤ H * g.inner (e z) w w)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) z v v ≤ (H * A + A * G) * ‖v‖ ^ 2 := by
  let T := mfderiv (𝓡 n) (𝓡 n) e z
  let Γ := CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) z
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hmetric' (w : EuclideanSpace ℝ (Fin n)) :
      g.inner (e z) (T w) (T w) ≤ A * ‖w‖ ^ 2 := by
    simpa only [RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply] using! hmetric w
  have hnorm (w : EuclideanSpace ℝ (Fin n)) :
      g.tangentNorm (e z) (T w) ≤ A * ‖w‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hA0 (norm_nonneg _), (hmetric' w).trans ?_⟩
    have hAA : A ≤ A ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hAA (sq_nonneg ‖w‖)]
  have hez := he.contMDiffAt (e.open_source.mem_nhds hz)
  have hfirst (w : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ (f ∘ e) z w| ≤ A * ‖w‖ := by
    have heq := congrArg (fun F => F w)
      (mfderiv_comp z (hf.mdifferentiableAt (by simp)) (hez.mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change fderiv ℝ (f ∘ e) z w = mvfderiv (𝓡 n) f (e z) (T w) at heq
    rw [heq]
    have h := D.abs_mvfderiv_le_gradient_norm f (e z) (T w)
    have hg : g.tangentNorm (e z) (D.gradient f (e z)) = 1 := by
      change Real.sqrt _ = 1
      rw [hgrad, Real.sqrt_one]
    rw [hg, one_mul] at h
    exact h.trans (hnorm w)
  have hΓ : ‖Γ v v‖ ≤ G * ‖v‖ ^ 2 :=
    (Γ.le_opNorm₂ v v).trans (by nlinarith [sq_nonneg ‖v‖])
  have hterm : fderiv ℝ (f ∘ e) z (Γ v v) ≤ A * G * ‖v‖ ^ 2 :=
    (le_abs_self _).trans ((hfirst _).trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hΓ hA0))
  have hHess := (hhess (T v)).trans (mul_le_mul_of_nonneg_left (hmetric' v) hH)
  have heq := D.hessian_in_smooth_local_parametrization e he hei hz hf v v
  change D.hessian f (e z) (T v) (T v) =
    fderiv ℝ (fderiv ℝ (f ∘ e)) z v v - fderiv ℝ (f ∘ e) z (Γ v v) at heq
  nlinarith

theorem intrinsic_bounds_of_parametrization (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ e.source)
    {f : M → ℝ} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e z))
    {b C L G : ℝ} (hb : 0 < b) (hC : 0 ≤ C) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hlow : ∀ v : EuclideanSpace ℝ (Fin n),
      b * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e z v v)
    (hfirst : ‖fderiv ℝ (f ∘ e) z‖ ≤ L)
    (hsecond : ∀ v : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ (f ∘ e)) z v v ≤ C * ‖v‖ ^ 2)
    (hconn : ‖CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients e) z‖ ≤ G) :
    g.tangentNorm (e z) (D.gradient f (e z)) ≤ L / Real.sqrt b ∧
    ∀ w : TangentSpace (𝓡 n) (e z),
      D.hessian f (e z) w w ≤ ((C + L * G) / b) * g.inner (e z) w w := by
  let T := mfderiv (𝓡 n) (𝓡 n) e z
  let Γ := CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) z
  have hlow' (v : EuclideanSpace ℝ (Fin n)) :
      b * ‖v‖ ^ 2 ≤ g.inner (e z) (T v) (T v) := by
    simpa only [RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply] using! hlow v
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hT : T.IsInvertible := ⟨heD.mfderiv hz, rfl⟩
  have hnorm (v : EuclideanSpace ℝ (Fin n)) :
      ‖v‖ ≤ g.tangentNorm (e z) (T v) / Real.sqrt b := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    have h := Real.sqrt_le_sqrt (hlow' v)
    simpa +instances only [Real.sqrt_mul hb.le, Real.sqrt_sq (norm_nonneg v),
      RiemannianMetric.tangentNorm, mul_comm] using h
  have hfirst' (v : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ (f ∘ e) z v| ≤ L * ‖v‖ :=
    ((fderiv ℝ (f ∘ e) z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hfirst (norm_nonneg v))
  constructor
  · apply (D.gradient_norm_le_iff f (e z) (by positivity)).mpr
    intro w
    obtain ⟨v, rfl⟩ := hT.surjective w
    have hez := he.contMDiffAt (e.open_source.mem_nhds hz)
    have heq := congrArg (fun F => F v)
      (mfderiv_comp z (hf.mdifferentiableAt (by simp)) (hez.mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change fderiv ℝ (f ∘ e) z v = mvfderiv (𝓡 n) f (e z) (T v) at heq
    rw [← heq]
    exact (hfirst' v).trans (by
      simpa [div_mul_eq_mul_div, mul_div_assoc] using
        mul_le_mul_of_nonneg_left (hnorm v) hL)
  · intro w
    obtain ⟨v, rfl⟩ := hT.surjective w
    have hΓ : ‖Γ v v‖ ≤ G * ‖v‖ ^ 2 :=
      (Γ.le_opNorm₂ v v).trans (by nlinarith [sq_nonneg ‖v‖])
    have hterm : -fderiv ℝ (f ∘ e) z (Γ v v) ≤ L * G * ‖v‖ ^ 2 :=
      (neg_le_abs _).trans ((hfirst' _).trans (by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hΓ hL))
    have hcoord : D.hessian f (e z) (T v) (T v) ≤ (C + L * G) * ‖v‖ ^ 2 := by
      rw [D.hessian_in_smooth_local_parametrization e he hei hz hf]
      change fderiv ℝ (fderiv ℝ (f ∘ e)) z v v -
        fderiv ℝ (f ∘ e) z (Γ v v) ≤ _
      nlinarith [hsecond v]
    apply hcoord.trans
    have hsquare : ‖v‖ ^ 2 ≤ g.inner (e z) (T v) (T v) / b :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hlow' v)
    simpa only [div_mul_eq_mul_div, mul_div_assoc] using
      mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ C + L * G)

end PoincareConjecture.LeviCivitaData
