import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorNorm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Powers








noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem sum_inner_connection_smul_eq (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x} {φ : M → ℝ} {x : M}
    (hV : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% V) x)
    (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ x) :
    (∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
      (D.connection (fun y => φ y • V y) x (g.orthonormalBasis x i))) =
      φ x * (∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection V x (g.orthonormalBasis x i))) +
      (1 / 2 : ℝ) * g.inner x (D.gradient φ x)
        (D.gradient (fun y => g.inner y (V y) (V y)) x) := by
  have hterm (i) :
      g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection (fun y => φ y • V y) x (g.orthonormalBasis x i)) =
      φ x * g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection V x (g.orthonormalBasis x i)) +
      (1 / 2 : ℝ) * (mvfderiv (𝓡 n) φ x (g.orthonormalBasis x i) *
        mvfderiv (𝓡 n) (fun y => g.inner y (V y) (V y)) x (g.orthonormalBasis x i)) := by
    change g.inner x (D.connection V x (g.orthonormalBasis x i))
      (D.connection (φ • V) x (g.orthonormalBasis x i)) = _
    rw [D.connection.isCovariantDerivativeOn.leibniz hV hφ,
      D.mvfderiv_normSq hV]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul, smul_eq_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    D.sum_mvfderiv_mul_eq_inner_gradient]



theorem sum_inner_connection_regularized_power_cross (D : LeviCivitaData g)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) (x : M) :
    let w := fun y => Real.sqrt (g.inner y (V y) (V y) + ε)
    (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
      (D.connection (fun y => (η y ^ 2 * w y ^ (2 * p - 2)) • V y) x
        (g.orthonormalBasis x i))) =
      η x ^ 2 * w x ^ (2 * p - 2) *
        (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
          (D.connection V x (g.orthonormalBasis x i))) +
      2 * η x * w x ^ (2 * p - 2) *
        (∑ i, mvfderiv (𝓡 n) η x (g.orthonormalBasis x i) *
          g.inner x (D.connection X x (g.orthonormalBasis x i)) (V x)) +
      (2 * p - 2) * η x ^ 2 * w x ^ (2 * p - 3) *
        (∑ i, mvfderiv (𝓡 n) w x (g.orthonormalBasis x i) *
          g.inner x (D.connection X x (g.orthonormalBasis x i)) (V x)) := by
  let w := fun y => Real.sqrt (g.inner y (V y) (V y) + ε)
  let φ := fun y => η y ^ 2 * w y ^ (2 * p - 2)
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := contMDiff_regularized_vector_norm hV hε
  have hwpos (y : M) : 0 < w y := regularized_vector_norm_pos (g := g) V hε y
  have hpower := contMDiff_rpow_of_pos hw hwpos (2 * p - 2)
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ := (hη.pow 2).mul hpower
  have hηsq : D.gradient (fun y => η y ^ 2) x =
      η x • D.gradient η x + η x • D.gradient η x := by
    simpa only [pow_two] using D.gradient_mul
      ((hη x).mdifferentiableAt (by simp)) ((hη x).mdifferentiableAt (by simp))
  have hφder (v : TangentSpace (𝓡 n) x) : mvfderiv (𝓡 n) φ x v =
      2 * η x * w x ^ (2 * p - 2) * mvfderiv (𝓡 n) η x v +
      (2 * p - 2) * η x ^ 2 * w x ^ (2 * p - 3) * mvfderiv (𝓡 n) w x v := by
    rw [← D.inner_gradient]
    dsimp only [φ]
    rw [D.gradient_mul (((hη.pow 2) x).mdifferentiableAt (by simp))
      ((hpower x).mdifferentiableAt (by simp)), D.gradient_rpow_of_pos hw hwpos, hηsq]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, D.inner_gradient,
      show 2 * p - 2 - 1 = 2 * p - 3 by ring]
    ring
  have hterm (i) :
      g.inner x (D.connection X x (g.orthonormalBasis x i))
        (D.connection (fun y => φ y • V y) x (g.orthonormalBasis x i)) =
      η x ^ 2 * w x ^ (2 * p - 2) *
        g.inner x (D.connection X x (g.orthonormalBasis x i))
          (D.connection V x (g.orthonormalBasis x i)) +
      (2 * η x * w x ^ (2 * p - 2)) *
        (mvfderiv (𝓡 n) η x (g.orthonormalBasis x i) *
          g.inner x (D.connection X x (g.orthonormalBasis x i)) (V x)) +
      ((2 * p - 2) * η x ^ 2 * w x ^ (2 * p - 3)) *
        (mvfderiv (𝓡 n) w x (g.orthonormalBasis x i) *
          g.inner x (D.connection X x (g.orthonormalBasis x i)) (V x)) := by
    change g.inner x (D.connection X x (g.orthonormalBasis x i))
      (D.connection (φ • V) x (g.orthonormalBasis x i)) = _
    rw [D.connection.isCovariantDerivativeOn.leibniz
      ((hV x).mdifferentiableAt (by simp)) ((hφ x).mdifferentiableAt (by simp))]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul, smul_eq_mul, hφder]
    dsimp only [φ]
    ring
  change (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
    (D.connection (fun y => φ y • V y) x (g.orthonormalBasis x i))) = _
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, w]



theorem sum_inner_connection_regularized_power (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) (x : M) :
    let w := fun y => Real.sqrt (g.inner y (V y) (V y) + ε)
    (∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
      (D.connection (fun y => (η y ^ 2 * w y ^ (2 * p - 2)) • V y) x
        (g.orthonormalBasis x i))) =
      η x ^ 2 * w x ^ (2 * p - 2) *
        (∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
          (D.connection V x (g.orthonormalBasis x i))) +
      (2 * p - 2) * η x ^ 2 * w x ^ (2 * p - 2) *
        g.inner x (D.gradient w x) (D.gradient w x) +
      2 * η x * w x ^ (2 * p - 1) * g.inner x (D.gradient η x) (D.gradient w x) := by
  let Q := fun y => g.inner y (V y) (V y)
  let w := fun y => Real.sqrt (Q y + ε)
  let φ := fun y => η y ^ 2 * w y ^ (2 * p - 2)
  have hQ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ Q := contMDiff_vector_normSq hV
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := contMDiff_regularized_vector_norm hV hε
  have hwpos (y : M) : 0 < w y := regularized_vector_norm_pos (g := g) V hε y
  have hwsq (y : M) : w y ^ 2 = Q y + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp (hwpos y)).le
  have hshift (y : M) : mvfderiv (𝓡 n) (fun z => Q z + ε) y =
      mvfderiv (𝓡 n) Q y := by
    simpa only [mvfderiv_const, add_zero] using
      mvfderiv_fun_add ((hQ y).mdifferentiableAt (by simp))
        (mdifferentiableAt_const (c := ε))
  have hgshift : D.gradient (fun y => Q y + ε) x = D.gradient Q x := by
    simp only [gradient, hshift]
  have hgrad := D.gradient_mul ((hw x).mdifferentiableAt (by simp))
    ((hw x).mdifferentiableAt (by simp))
  change D.gradient (fun y => w y * w y) x =
    w x • D.gradient w x + w x • D.gradient w x at hgrad
  simp only [← pow_two, hwsq, hgshift] at hgrad
  have hηsq : D.gradient (fun y => η y ^ 2) x =
      η x • D.gradient η x + η x • D.gradient η x := by
    simpa only [pow_two] using D.gradient_mul
      ((hη x).mdifferentiableAt (by simp)) ((hη x).mdifferentiableAt (by simp))
  have hpower := contMDiff_rpow_of_pos hw hwpos (2 * p - 2)
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ := (hη.pow 2).mul hpower
  have hpow1 : w x ^ (2 * p - 2 - 1) * w x = w x ^ (2 * p - 2) := by
    rw [← Real.rpow_add_one (hwpos x).ne', sub_add_cancel]
  have hpow2 : w x ^ (2 * p - 2) * w x = w x ^ (2 * p - 1) := by
    rw [← Real.rpow_add_one (hwpos x).ne']
    congr 1
    ring
  change (∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
    (D.connection (fun y => φ y • V y) x (g.orthonormalBasis x i))) = _
  rw [D.sum_inner_connection_smul_eq ((hV x).mdifferentiableAt (by simp))
    ((hφ x).mdifferentiableAt (by simp))]
  change φ x * _ + (1 / 2 : ℝ) * g.inner x (D.gradient φ x) (D.gradient Q x) = _
  calc
    _ = η x ^ 2 * w x ^ (2 * p - 2) *
        (∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
          (D.connection V x (g.orthonormalBasis x i))) +
        (2 * p - 2) * η x ^ 2 * (w x ^ (2 * p - 2 - 1) * w x) *
          g.inner x (D.gradient w x) (D.gradient w x) +
        2 * η x * (w x ^ (2 * p - 2) * w x) *
          g.inner x (D.gradient η x) (D.gradient w x) := by
      dsimp only [φ]
      rw [D.gradient_mul (((hη.pow 2) x).mdifferentiableAt (by simp))
        ((hpower x).mdifferentiableAt (by simp)), D.gradient_rpow_of_pos hw hwpos,
        hηsq, hgrad]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring
    _ = _ := by rw [hpow1, hpow2]

end PoincareConjecture.LeviCivitaData
