import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Extrema










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35.Uniqueness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem fixed_tensorNorm_sq {r : ℕ}
    (H : CovariantTensorEvaluation n M r) (x : M) :
    (g.tensorNorm H x) ^ 2 =
      ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        H x (fun i => g.orthonormalBasis x (a i)) ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)



theorem fixed_tensorNorm_sq_hasDerivWithinAt {r : ℕ} {J : Set ℝ} {t : ℝ}
    (H : ℝ → CovariantTensorEvaluation n M r) (R : CovariantTensorEvaluation n M r)
    (x : M) (hd : ∀ v, HasDerivWithinAt (fun s => H s x v) (R x v) J t) :
    HasDerivWithinAt (fun s => (g.tensorNorm (H s) x) ^ 2)
      (2 * ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        H t x (fun i => g.orthonormalBasis x (a i)) *
          R x (fun i => g.orthonormalBasis x (a i))) J t := by
  have heq : (fun s => (g.tensorNorm (H s) x) ^ 2) = fun s =>
      ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        H s x (fun i => g.orthonormalBasis x (a i)) ^ 2 := by
    funext s
    exact fixed_tensorNorm_sq (H s) x
  rw [heq]
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Finset.mul_sum, mul_assoc,
    Pi.pow_apply] using
    HasDerivWithinAt.fun_sum (u := Finset.univ)
      (fun (a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) _ =>
        (hd (fun i => g.orthonormalBasis x (a i))).pow 2)


theorem fixed_tensor_pairing_le {r : ℕ}
    (H R : CovariantTensorEvaluation n M r) (x : M) :
    (∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      H x (fun i => g.orthonormalBasis x (a i)) *
        R x (fun i => g.orthonormalBasis x (a i))) ≤
      g.tensorNorm H x * g.tensorNorm R x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      H x (fun i => g.orthonormalBasis x (a i)))
    (fun a => R x (fun i => g.orthonormalBasis x (a i)))
  rw [← fixed_tensorNorm_sq H x, ← fixed_tensorNorm_sq R x] at h
  have hp : 0 ≤ g.tensorNorm H x * g.tensorNorm R x :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith



theorem tensor_principal_pairing_le_at_norm_max {r m : ℕ}
    (D : LeviCivitaData g) {H : CovariantTensorEvaluation n M r}
    (hH : IsSmoothCovariantTensor H) (x : M)
    (e : Fin m → TangentSpace (𝓡 n) x)
    (hmax : IsLocalMax (fun y => (g.tensorNorm H y) ^ 2) x) :
    (∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      H x (fun j => g.orthonormalBasis x (a j)) *
        ∑ i : Fin m, D.iteratedCovariantTensorDerivative H 2 x
          (Fin.cons (e i) (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))))) ≤
      -(∑ i : Fin m,
        ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          D.covariantTensorDerivative H x
            (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))) ^ 2) := by
  have hi (i : Fin m) :
      (∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        H x (fun j => g.orthonormalBasis x (a j)) *
          D.iteratedCovariantTensorDerivative H 2 x
            (Fin.cons (e i) (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))))) ≤
        -(∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          D.covariantTensorDerivative H x
            (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))) ^ 2) := by
    have h := D.hessian_nonpos_of_isLocalMax (M04.contMDiff_tensorNorm_sq g hH) hmax (e i)
    rw [M04.hessian_tensorNorm_sq D hH] at h
    simp only [← pow_two] at h
    linarith only [h]
  calc
    _ = ∑ i : Fin m,
        ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          H x (fun j => g.orthonormalBasis x (a j)) *
            D.iteratedCovariantTensorDerivative H 2 x
              (Fin.cons (e i) (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j)))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin m,
        -(∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          D.covariantTensorDerivative H x
            (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))) ^ 2) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = _ := by rw [Finset.sum_neg_distrib]



theorem tensor_norm_maximum_velocity {r m : ℕ} {J : Set ℝ} {t : ℝ}
    (D : LeviCivitaData g) (H : ℝ → CovariantTensorEvaluation n M r)
    (R : CovariantTensorEvaluation n M r) (hH : IsSmoothCovariantTensor (H t))
    (x : M) (e : Fin m → TangentSpace (𝓡 n) x)
    {c B : ℝ} (hc : 0 < c)
    (hmax : IsLocalMax (fun y => (g.tensorNorm (H t) y) ^ 2) x)
    (hheat : ∀ v, HasDerivWithinAt (fun s => H s x v)
      ((∑ i : Fin m, D.iteratedCovariantTensorDerivative (H t) 2 x
        (Fin.cons (e i) (Fin.cons (e i) v))) + R x v) J t)
    (hell : c * (g.tensorNorm (D.covariantTensorDerivative (H t)) x) ^ 2 ≤
      ∑ i : Fin m,
        ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          D.covariantTensorDerivative (H t) x
            (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))) ^ 2)
    (hR : g.tensorNorm R x ≤ B *
      (g.tensorNorm (H t) x + g.tensorNorm (D.covariantTensorDerivative (H t)) x)) :
    ∃ d : ℝ, HasDerivWithinAt (fun s => (g.tensorNorm (H s) x) ^ 2) d J t ∧
      d ≤ (2 * B + B ^ 2 / c) * (g.tensorNorm (H t) x) ^ 2 := by
  let P := ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
    H t x (fun j => g.orthonormalBasis x (a j)) *
      ∑ i : Fin m, D.iteratedCovariantTensorDerivative (H t) 2 x
        (Fin.cons (e i) (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))))
  let Q := ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
    H t x (fun j => g.orthonormalBasis x (a j)) *
      R x (fun j => g.orthonormalBasis x (a j))
  have hd := fixed_tensorNorm_sq_hasDerivWithinAt (g := g) H
    (fun y v => (∑ i : Fin m, D.iteratedCovariantTensorDerivative (H t) 2 y
      (Fin.cons (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (e i) y)
        (Fin.cons (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (e i) y) v))) + R y v)
    x (by simpa only [FiberBundle.extend_apply_self] using hheat)
  have hdeq :
      2 * (∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        H t x (fun j => g.orthonormalBasis x (a j)) *
          ((∑ i : Fin m, D.iteratedCovariantTensorDerivative (H t) 2 x
            (Fin.cons (e i) (Fin.cons (e i) (fun j => g.orthonormalBasis x (a j))))) +
              R x (fun j => g.orthonormalBasis x (a j)))) = 2 * (P + Q) := by
    simp only [mul_add, Finset.sum_add_distrib, P, Q]
  simp only [FiberBundle.extend_apply_self] at hd
  rw [hdeq] at hd
  refine ⟨2 * (P + Q), hd, ?_⟩
  let N := g.tensorNorm (H t) x
  let G := g.tensorNorm (D.covariantTensorDerivative (H t)) x
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hP : P ≤ -(c * G ^ 2) :=
    (tensor_principal_pairing_le_at_norm_max D hH x e hmax).trans (neg_le_neg hell)
  have hQ : Q ≤ N * (B * (N + G)) :=
    (fixed_tensor_pairing_le (g := g) (H t) R x).trans (mul_le_mul_of_nonneg_left hR hN)
  have hdiv : c * (B ^ 2 / c) = B ^ 2 := mul_div_cancel₀ _ hc.ne'
  have hyoung : 2 * B * N * G ≤ c * G ^ 2 + (B ^ 2 / c) * N ^ 2 := by
    have hs := sq_nonneg (c * G - B * N)
    have hd := congrArg (fun z : ℝ => z * N ^ 2) hdiv
    nlinarith
  change 2 * (P + Q) ≤ (2 * B + B ^ 2 / c) * N ^ 2
  nlinarith [mul_nonneg hc.le (sq_nonneg G)]

end PoincareConjecture.M35.Uniqueness
