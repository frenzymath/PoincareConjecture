import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorDecodeNative
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

noncomputable section

universe u v

namespace PoincareConjecture.ParsevalTensorNative

open TensorProbeNative (Coefficients)

section LinearAlgebra

variable {V iota : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype iota]

theorem parseval_sum_sq (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v) (v : V) :
    (∑ a, inner ℝ (F a) v ^ 2) = ‖v‖ ^ 2 := by
  calc
    (∑ a, inner ℝ (F a) v ^ 2) = inner ℝ (∑ a, inner ℝ (F a) v • F a) v := by
      simp only [sum_inner, real_inner_smul_left, pow_two]
    _ = inner ℝ v v := by rw [hF v]
    _ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v

theorem decode_abs_le (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v)
    (C : Coefficients iota) (v w : V) :
    |decode F C v w| ≤ ‖C‖ * ‖v‖ * ‖w‖ := by
  let Q : Coefficients iota := WithLp.toLp 2
    (fun ab : iota × iota => inner ℝ (F ab.1) v * inner ℝ (F ab.2) w)
  have hQsq : ‖Q‖ ^ 2 = (‖v‖ * ‖w‖) ^ 2 := by
    calc
      ‖Q‖ ^ 2 = (∑ a, inner ℝ (F a) v ^ 2) *
          ∑ b, inner ℝ (F b) w ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        change (∑ ab : iota × iota,
          (inner ℝ (F ab.1) v * inner ℝ (F ab.2) w) ^ 2) = _
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        simp only [mul_pow]
      _ = (‖v‖ * ‖w‖) ^ 2 := by
        rw [parseval_sum_sq F hF v, parseval_sum_sq F hF w, mul_pow]
  have hQ : ‖Q‖ = ‖v‖ * ‖w‖ :=
    (sq_eq_sq₀ (norm_nonneg Q) (mul_nonneg (norm_nonneg v) (norm_nonneg w))).mp hQsq
  have heq : decode F C v w = inner ℝ C Q := by
    rw [decode_apply, coefficient_inner]
    apply Finset.sum_congr rfl
    intro ab _
    change C ab * inner ℝ (F ab.1) v * inner ℝ (F ab.2) w =
      C ab * (inner ℝ (F ab.1) v * inner ℝ (F ab.2) w)
    ring
  rw [heq]
  calc
    |inner ℝ C Q| ≤ ‖C‖ * ‖Q‖ := abs_real_inner_le_norm C Q
    _ = ‖C‖ * ‖v‖ * ‖w‖ := by rw [hQ, mul_assoc]

end LinearAlgebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type v} [Fintype iota]

theorem nativeDecode_diagonal_bound (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (x : M) (C : Coefficients iota) (v : TangentSpace (𝓡 n) x) :
    |nativeDecode g F x C v v| ≤ ‖C‖ * g.inner x v v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  calc
    |nativeDecode g F x C v v| ≤ ‖C‖ * ‖v‖ * ‖v‖ :=
      decode_abs_le (fun a => F a x) (hF x) C v v
    _ = ‖C‖ * g.inner x v v := by
      rw [mul_assoc, ← real_inner_self_eq_norm_mul_norm]
      rfl

theorem nativeDecode_symmetric (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (x : M) (C : Coefficients iota) (hC : ∀ a b, C (a, b) = C (b, a))
    (v w : TangentSpace (𝓡 n) x) :
    nativeDecode g F x C v w = nativeDecode g F x C w v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact decode_symmetric (fun a => F a x) C hC v w

theorem nativeDecode_zero (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M)) (x : M) :
    nativeDecode g F x 0 = 0 := by
  ext v w
  simp only [nativeDecode_apply, PiLp.zero_apply, zero_mul, Finset.sum_const_zero,
    ContinuousLinearMap.zero_apply]

theorem nativeDecode_hasDerivWithinAt (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (x : M) (C : ℝ → Coefficients iota) (D : Coefficients iota)
    {J : Set ℝ} {t : ℝ}
    (hC : ∀ ab : iota × iota, HasDerivWithinAt (fun s => C s ab) (D ab) J t)
    (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => nativeDecode g F x (C s) v w)
      (nativeDecode g F x D v w) J t := by
  simp only [nativeDecode_apply]
  exact HasDerivWithinAt.fun_sum (fun ab _ =>
    ((hC ab).mul_const (g.inner x (F ab.1 x) v)).mul_const (g.inner x (F ab.2 x) w))

end PoincareConjecture.ParsevalTensorNative

end
