import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.M13.TangentIsometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]

theorem tensorNorm_eq_of_homothety
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q)
    {k : ℕ} (S : CovariantTensorEvaluation n M k)
    (T : CovariantTensorEvaluation n N k)
    (x : M)
    (hST : ∀ v, S x v = T (f x)
      (fun i ↦ mfderiv (𝓡 n) (𝓡 n) f x (v i)))
    (A : MultilinearMap ℝ (fun _ : Fin k ↦ TangentSpace (𝓡 n) (f x)) ℝ)
    (hA : ∀ v, T (f x) v = A v) :
    h.tensorNorm T (f x) = (Real.sqrt Q)⁻¹ ^ k * g.tensorNorm S x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e := M13.homothetyTangentIsometry g h f Q hQ hf x
  have hemetric (u v : TangentSpace (𝓡 n) x) :
      h.inner (f x) (e u) (e v) = g.inner x u v := by
    change inner ℝ (e u) (e v) = inner ℝ u v
    exact e.inner_map_map u v
  have hscale (v : Fin k → TangentSpace (𝓡 n) x) :
      S x v = (Real.sqrt Q) ^ k * T (f x) (fun i ↦ e (v i)) := by
    rw [hST v]
    simp_rw [hA]
    simp only [e, M13.homothetyTangentIsometry_apply]
    rw [A.map_smul_univ]
    simp only [smul_eq_mul]
    rw [Finset.prod_const]
    simp only [Finset.card_fin]
    have hsqrt : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
    have hpow : (Real.sqrt Q) ^ k * (Real.sqrt Q)⁻¹ ^ k = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hsqrt, one_pow]
    rw [← mul_assoc, hpow, one_mul]
  let c : ℝ := (Real.sqrt Q)⁻¹ ^ k
  have hcpos : 0 < c := by
    dsimp [c]
    exact pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr hQ)) _
  have hcc : c * (Real.sqrt Q) ^ k = 1 := by
    dsimp [c]
    have hsqrt : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ hsqrt)
  let S' : CovariantTensorEvaluation n M k := fun _ v ↦ c * S x v
  have hS' (v : Fin k → TangentSpace (𝓡 n) x) :
      S' x v = T (f x) (fun i ↦ e (v i)) := by
    dsimp [S']
    calc
      c * S x v = c * ((Real.sqrt Q) ^ k * T (f x) (fun i ↦ e (v i))) := by
        rw [hscale v]
      _ = T (f x) (fun i ↦ e (v i)) := by
        rw [← mul_assoc, hcc, one_mul]
  have hnorm' : g.tensorNorm S' x = h.tensorNorm T (f x) := by
    apply g.tensorNorm_eq_of_linearEquiv h S' T x (f x) e.toLinearEquiv
      hemetric hS' A hA
  have hscaleNorm : g.tensorNorm S' x = c * g.tensorNorm S x := by
    change Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (c * S x (fun i ↦ g.orthonormalBasis x (a i))) ^ 2) =
      c * Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (S x (fun i ↦ g.orthonormalBasis x (a i))) ^ 2)
    calc
      Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (c * S x (fun i ↦ g.orthonormalBasis x (a i))) ^ 2) =
          Real.sqrt (c ^ 2 * ∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
            (S x (fun i ↦ g.orthonormalBasis x (a i))) ^ 2) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = Real.sqrt (c ^ 2) *
          Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (S x (fun i ↦ g.orthonormalBasis x (a i))) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg c)]
      _ = c * Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (S x (fun i ↦ g.orthonormalBasis x (a i))) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hcpos]
  calc
    h.tensorNorm T (f x) = g.tensorNorm S' x := hnorm'.symm
    _ = c * g.tensorNorm S x := hscaleNorm

end PoincareConjecture.M28
