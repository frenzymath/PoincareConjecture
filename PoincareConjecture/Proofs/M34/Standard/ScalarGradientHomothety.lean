import PoincareConjecture.Proofs.M34.Standard.ScalarGradientNorm
import PoincareConjecture.Proofs.M34.Standard.LocalHomothetyCurvature
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Scaling

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] [T2Space N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem mvfderiv_scalarCurvature_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) D.scalarCurvature x v =
      mvfderiv (𝓡 n) D'.scalarCurvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) / Q := by
  have heq : D.scalarCurvature =ᶠ[𝓝 x]
      (fun y => Q⁻¹ * D'.scalarCurvature (f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [div_eq_mul_inv, mul_comm] using
      D.scalarCurvature_eq_of_local_homothety D' hQ hU hf hmetric hy
  have hd : mvfderiv (𝓡 n) D.scalarCurvature x =
      mvfderiv (𝓡 n) (fun y => Q⁻¹ * D'.scalarCurvature (f y)) x :=
    heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))
  rw [hd, mvfderiv_const_mul]
  have hcomp := mvfderiv_comp x
    ((M34.contMDiff_scalarCurvature D').mdifferentiableAt (by simp))
    (((hf x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
  rw [show (fun y => D'.scalarCurvature (f y)) = D'.scalarCurvature ∘ f from rfl,
    hcomp]
  change Q⁻¹ * _ = _ / Q
  rw [div_eq_mul_inv, mul_comm]
  rfl

theorem mfderiv_gradient_scalarCurvature_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    mfderiv (𝓡 n) (𝓡 n) f x (D.gradient D.scalarCurvature x) =
      (Q ^ 2)⁻¹ • D'.gradient D'.scalarCurvature (f x) := by
  have hbij := g.mfderiv_bijective_of_pullback_eq (M13.scaleSmoothMetric h Q hQ) x
    (fun u v => (hmetric x hx u v).symm)
  apply (h.inner_isInvertible (f x)).injective
  ext w
  obtain ⟨v, rfl⟩ := hbij.2 w
  have hm := hmetric x hx (D.gradient D.scalarCurvature x) v
  rw [D.inner_gradient,
    D.mvfderiv_scalarCurvature_of_local_homothety D' hQ hU hf hmetric hx] at hm
  simp only [map_smul, smul_apply, smul_eq_mul, D'.inner_gradient]
  field_simp [hQ.ne'] at hm ⊢
  nlinarith

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture

theorem scalarGradientNorm_eq_of_local_homothety
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u)
        (mfderiv (𝓡 3) (𝓡 3) f y v))
    {x : M} (hx : x ∈ U) :
    scalarGradientNorm g D x = scalarGradientNorm h D' (f x) / Q ^ (3 / 2 : ℝ) := by
  rw [scalarGradientNorm_eq_tangentNorm, scalarGradientNorm_eq_tangentNorm]
  have hnorm : g.tangentNorm x (D.gradient D.scalarCurvature x) =
      Real.sqrt Q * h.tangentNorm (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x (D.gradient D.scalarCurvature x)) := by
    unfold RiemannianMetric.tangentNorm
    rw [hmetric x hx, Real.sqrt_mul hQ.le]
  rw [hnorm, D.mfderiv_gradient_scalarCurvature_of_local_homothety
    D' hQ hU hf hmetric hx]
  have hsmul : h.tangentNorm (f x) ((Q ^ 2)⁻¹ • D'.gradient D'.scalarCurvature (f x)) =
      (Q ^ 2)⁻¹ * h.tangentNorm (f x) (D'.gradient D'.scalarCurvature (f x)) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    change ‖(Q ^ 2)⁻¹ • D'.gradient D'.scalarCurvature (f x)‖ =
      (Q ^ 2)⁻¹ * ‖D'.gradient D'.scalarCurvature (f x)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hrpow : Q ^ (3 / 2 : ℝ) = Q * Real.sqrt Q := by
    calc
      Q ^ (3 / 2 : ℝ) = Q ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = Q * Real.sqrt Q := by rw [Real.rpow_add hQ, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hsmul, hrpow]
  field_simp [hQ.ne', (Real.sqrt_pos.mpr hQ).ne']
  ring_nf
  rw [Real.sq_sqrt hQ.le]
  ring

end PoincareConjecture
