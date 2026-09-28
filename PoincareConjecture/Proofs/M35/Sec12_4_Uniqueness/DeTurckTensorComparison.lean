import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.DeTurckEllipticity
import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.DeTurckMaximum
import PoincareConjecture.Proofs.M04.TensorNormBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35.Uniqueness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}




theorem tensor_eq_zero_of_principal_equation {r : ℕ} {T C B : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hB : 0 ≤ B) (D : LeviCivitaData g)
    (k : ℝ → RiemannianMetric n M)
    (H R : ℝ → CovariantTensorEvaluation n M r)
    (hH : ∀ t ∈ Icc 0 T, IsSmoothCovariantTensor (H t))
    (hcont : ContinuousOn (fun p : ℝ × M => (g.tensorNorm (H p.1) p.2) ^ 2)
      (Icc 0 T ×ˢ univ))
    (hinit : ∀ x v, H 0 x v = 0)
    (hdom : ∀ t ∈ Icc 0 T, ∀ x v, (k t).inner x v v ≤ C * g.inner x v v)
    (hend : ∀ ε > 0, ∀ x : M, ∃ K : Set M, IsCompact K ∧ x ∈ K ∧
      ∀ t ∈ Icc 0 T, ∀ y ∈ K \ interior K, (g.tensorNorm (H t) y) ^ 2 ≤ ε)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x v,
      HasDerivWithinAt (fun s => H s x v)
        ((∑ i, D.iteratedCovariantTensorDerivative (H t) 2 x
          (Fin.cons ((k t).orthonormalBasis x i)
            (Fin.cons ((k t).orthonormalBasis x i) v))) + R t x v) (Icc 0 T) t)
    (hresidual : ∀ t ∈ Ioc 0 T, ∀ x,
      g.tensorNorm (R t) x ≤ B *
        (g.tensorNorm (H t) x + g.tensorNorm (D.covariantTensorDerivative (H t)) x)) :
    ∀ t ∈ Icc 0 T, ∀ x v, H t x v = 0 := by
  let c := ((n : ℝ) * C + 1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  let L := 2 * B + B ^ 2 / c
  have hL : 0 ≤ L := add_nonneg (mul_nonneg zero_le_two hB) (div_nonneg (sq_nonneg _) hc.le)
  let v : ℝ → M → ℝ := fun t x => (g.tensorNorm (H t) x) ^ 2
  have hvinit (x : M) : v 0 x ≤ 0 := by
    simp only [v, RiemannianMetric.tensorNorm, hinit, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero, le_refl]
  have hvelocity (t : ℝ) (ht : t ∈ Ioc 0 T) (x : M)
      (hmax : IsLocalMax (v t) x) (_hpos : 0 < v t x) :
      ∃ d : ℝ, HasDerivWithinAt (fun s => v s x) d (Icc 0 T) t ∧ d ≤ L * v t x := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hell := tensor_first_slot_trace_coercive g (k t)
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D (hH t ht')) x hC
      (hdom t ht' x)
    exact tensor_norm_maximum_velocity D H (R t) (hH t ht') x
      ((k t).orthonormalBasis x) hc hmax (hheat t ht x) hell (hresidual t ht x)
  have hzero := nonpositive_of_uniform_end_and_maximum_velocity hT hL v hcont
    hvinit hend hvelocity
  intro t ht x w
  have hsq : (g.tensorNorm (H t) x) ^ 2 = 0 :=
    le_antisymm (hzero t ht x) (sq_nonneg _)
  have heval := M04.tensorEvaluation_sq_le_tensorNorm g (hH t ht) x w
  rw [hsq, zero_mul] at heval
  exact sq_eq_zero_iff.mp (le_antisymm heval (sq_nonneg _))

end PoincareConjecture.M35.Uniqueness
