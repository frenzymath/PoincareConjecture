import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.GradientTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiff_vector_normSq
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => g.inner x (V x) (V x)) := by
  intro x
  have h := ((g.contMDiff x).clm_bundle_apply (hV x)).clm_bundle_apply (hV x)
  exact (Bundle.contMDiffAt_totalSpace.mp h).2

theorem gradient_vector_normSq_le (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hV : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% V) x) :
    let Q := fun y => g.inner y (V y) (V y)
    g.inner x (D.gradient Q x) (D.gradient Q x) ≤
      4 * Q x * ∑ i, g.inner x
        (D.connection V x (g.orthonormalBasis x i))
        (D.connection V x (g.orthonormalBasis x i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  rw [D.gradient_normSq_eq_sum_mvfderiv_sq]
  simp_rw [D.mvfderiv_normSq hV]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := real_inner_mul_inner_self_le
    (D.connection V x (g.orthonormalBasis x i)) (V x)
  change (2 * inner ℝ (D.connection V x (g.orthonormalBasis x i)) (V x)) ^ 2 ≤
    4 * inner ℝ (V x) (V x) *
      inner ℝ (D.connection V x (g.orthonormalBasis x i))
        (D.connection V x (g.orthonormalBasis x i))
  nlinarith only [h]

theorem regularized_vector_norm_pos
    (V : (x : M) → TangentSpace (𝓡 n) x) {ε : ℝ} (hε : 0 < ε) (x : M) :
    0 < Real.sqrt (g.inner x (V x) (V x) + ε) := by
  have hQ : 0 ≤ g.inner x (V x) (V x) := by
    by_cases h : V x = 0
    · simp [h]
    · exact (g.pos x _ h).le
  exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hQ hε)

theorem contMDiff_regularized_vector_norm
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    {ε : ℝ} (hε : 0 < ε) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => Real.sqrt (g.inner x (V x) (V x) + ε)) := by
  intro x
  have hpos := Real.sqrt_pos.mp (regularized_vector_norm_pos (g := g) V hε x)
  exact (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp x
    ((contMDiff_vector_normSq (g := g) hV x).add contMDiffAt_const)

theorem gradient_regularized_vector_norm_le (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    let w := fun y => Real.sqrt (g.inner y (V y) (V y) + ε)
    g.inner x (D.gradient w x) (D.gradient w x) ≤
      ∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection V x (g.orthonormalBasis x i)) := by
  let Q := fun y => g.inner y (V y) (V y)
  let w := fun y => Real.sqrt (Q y + ε)
  let A := ∑ i, g.inner x (D.connection V x (g.orthonormalBasis x i))
    (D.connection V x (g.orthonormalBasis x i))
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro i _
    by_cases h : D.connection V x (g.orthonormalBasis x i) = 0
    · simp [h]
    · exact (g.pos x _ h).le
  have hwpos (y : M) : 0 < w y := regularized_vector_norm_pos (g := g) V hε y
  have hwsq (y : M) : w y ^ 2 = Q y + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp (hwpos y)).le
  have hQ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ Q := contMDiff_vector_normSq hV
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := contMDiff_regularized_vector_norm hV hε
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
  have hgradSq : g.inner x (D.gradient Q x) (D.gradient Q x) =
      4 * w x ^ 2 * g.inner x (D.gradient w x) (D.gradient w x) := by
    rw [hgrad]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hKato := D.gradient_vector_normSq_le ((hV x).mdifferentiableAt (by simp))
  change g.inner x (D.gradient Q x) (D.gradient Q x) ≤ 4 * Q x * A at hKato
  rw [hgradSq] at hKato
  change g.inner x (D.gradient w x) (D.gradient w x) ≤ A
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * w x ^ 2 from
    mul_pos (by norm_num) (sq_pos_of_pos (hwpos x)))).mp
  nlinarith only [hKato, congrArg (fun z => 4 * z * A) (hwsq x), mul_nonneg hε.le hA]

end PoincareConjecture.LeviCivitaData
