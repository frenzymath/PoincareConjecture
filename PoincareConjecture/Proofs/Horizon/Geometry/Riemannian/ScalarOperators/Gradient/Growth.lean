import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorNorm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient.LevelDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Symmetry
import Mathlib.Analysis.InnerProductSpace.Rayleigh










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators NNReal

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem connection_gradient_norm_le_of_hessian_bound
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (x : M) (hhess : ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v)
    (v : TangentSpace (𝓡 n) x) :
    g.tangentNorm x (D.connection (D.gradient f) x v) ≤ C * g.tangentNorm x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := D.connection (D.gradient f) x
  have hsym : A.IsSymmetric := by
    intro u w
    change g.inner x (A u) w = g.inner x u (A w)
    rw [g.symm x u, ← D.hessian_eq_inner_connection_gradient (hf x),
      ← D.hessian_eq_inner_connection_gradient (hf x)]
    exact D.hessian_symm hf x u w
  have hnorm : ‖A‖ ≤ C := by
    rw [A.norm_eq_iSup_rayleighQuotient hsym]
    apply ciSup_le
    intro w
    by_cases hw : w = 0
    · simp [hw, ContinuousLinearMap.rayleighQuotient, hC]
    have hpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    rw [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, abs_div,
      abs_of_pos hpos, div_le_iff₀ hpos]
    have h := hhess w
    rw [D.hessian_eq_inner_connection_gradient (hf x)] at h
    change |inner ℝ (A w) w| ≤ C * inner ℝ w w at h
    simpa only [real_inner_self_eq_norm_sq] using h
  exact (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))


theorem regularized_gradient_norm_gradient_le_of_hessian_bound
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hhess : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v)
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    g.tangentNorm x (D.gradient
      (fun y => Real.sqrt (g.inner y (D.gradient f y) (D.gradient f y) + ε)) x) ≤
        ((n : ℝ) + 1) * C := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hsum : (∑ i, g.inner x
      (D.connection (D.gradient f) x (g.orthonormalBasis x i))
      (D.connection (D.gradient f) x (g.orthonormalBasis x i))) ≤ (n : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), C ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := D.connection_gradient_norm_le_of_hessian_bound hf hC x (hhess x)
          (g.orthonormalBasis x i)
        have he : g.tangentNorm x (g.orthonormalBasis x i) = 1 :=
          (g.orthonormalBasis x).norm_eq_one i
        rw [he, mul_one] at h
        change inner ℝ (D.connection (D.gradient f) x (g.orthonormalBasis x i))
          (D.connection (D.gradient f) x (g.orthonormalBasis x i)) ≤ C ^ 2
        rw [real_inner_self_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by simp [hdim]
  have hk := (D.gradient_regularized_vector_norm_le (D.contMDiff_gradient hf) hε x).trans hsum
  have htarget : (n : ℝ) * C ^ 2 ≤ (((n : ℝ) + 1) * C) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg C,
      mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg C)]
  have hsqrt := Real.sqrt_le_sqrt (hk.trans htarget)
  rw [Real.sqrt_sq (mul_nonneg (by positivity) hC)] at hsqrt
  exact hsqrt

variable [T3Space M] [ConnectedSpace M]



theorem gradient_norm_le_base_add_of_hessian_bound
    (D : LeviCivitaData g) (hc : MetricComplete g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hhess : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v)
    (p x : M) :
    g.tangentNorm x (D.gradient f x) ≤ g.tangentNorm p (D.gradient f p) + 1 +
      (((n : ℝ) + 1) * C) * (g.edist p x).toReal := by
  let w := fun y => Real.sqrt (g.inner y (D.gradient f y) (D.gradient f y) + 1)
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w :=
    contMDiff_regularized_vector_norm (D.contMDiff_gradient hf) (by norm_num)
  let B : ℝ≥0 := ⟨((n : ℝ) + 1) * C, mul_nonneg (by positivity) hC⟩
  have hinc := g.abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall hc hw p x
    (L := B) (fun y _ => D.regularized_gradient_norm_gradient_le_of_hessian_bound
      hf hC hhess (by norm_num : (0 : ℝ) < 1) y)
  have hpx : w x ≤ w p + B * (g.edist p x).toReal := by
    linarith [(le_abs_self (w x - w p)).trans hinc]
  have hx : g.tangentNorm x (D.gradient f x) ≤ w x :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right zero_le_one)
  have hp : w p ≤ g.tangentNorm p (D.gradient f p) + 1 := by
    have hq : 0 ≤ g.inner p (D.gradient f p) (D.gradient f p) := by
      by_cases h : D.gradient f p = 0
      · simp [h]
      · exact (g.pos p _ h).le
    have hq1 : 0 ≤ g.inner p (D.gradient f p) (D.gradient f p) + 1 := by linarith
    have hsq := Real.sq_sqrt hq
    have hsq1 := Real.sq_sqrt hq1
    dsimp [w, RiemannianMetric.tangentNorm]
    nlinarith [Real.sqrt_nonneg (g.inner p (D.gradient f p) (D.gradient f p)),
      Real.sqrt_nonneg (g.inner p (D.gradient f p) (D.gradient f p) + 1)]
  change w x ≤ w p + ((n : ℝ) + 1) * C * (g.edist p x).toReal at hpx
  linarith

end PoincareConjecture.LeviCivitaData
