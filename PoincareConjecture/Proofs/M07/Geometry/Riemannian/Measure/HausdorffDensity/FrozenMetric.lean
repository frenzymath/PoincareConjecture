import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Density
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_frozenPullbackEquiv (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ v, ‖A v‖ = g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)) ∧
      |A.toContinuousLinearMap.det| = g.pullbackVolumeDensity f x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  let b : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) (f x)) :=
    (stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) (f x))).reindex
      (finCongr (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n; simp))
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    b.repr.toLinearMap.comp (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  have hL : Function.Injective L := b.repr.injective.comp hi
  let A := (LinearEquiv.ofBijective L
    ⟨hL, LinearMap.surjective_of_injective hL⟩).toContinuousLinearEquiv
  have hinner (v w : EuclideanSpace ℝ (Fin n)) :
      inner ℝ (A v) (A w) =
        g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
          (mfderiv (𝓡 n) (𝓡 n) f x w) := by
    change inner ℝ (b.repr _) (b.repr _) = _
    rw [b.repr.inner_map_map]
    rfl
  refine ⟨A, ?_, ?_⟩
  · intro v
    rw [norm_eq_sqrt_real_inner, tangentNorm, hinner]
  · have hdet := L.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
    rw [LinearMap.normDet_eq_abs_det] at hdet
    have heq : (Matrix.gram ℝ (fun i ↦ L (EuclideanSpace.basisFun (Fin n) ℝ i))) =
        Matrix.of (fun i j : Fin n => g.inner (f x)
          (mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ i))
          (mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ j))) := by
      ext i j
      exact hinner _ _
    rw [heq] at hdet
    unfold pullbackVolumeDensity
    rw [← hdet]
    change |L.det| = Real.sqrt (|L.det| ^ 2)
    rw [Real.sqrt_sq (abs_nonneg _)]

set_option backward.isDefEq.respectTransparency false in

theorem eventually_pullbackNorm_bounds (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ v, ‖A v‖ = g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∀ᶠ y in 𝓝 x, ∀ v : EuclideanSpace ℝ (Fin n),
      (1 - ε) * ‖A v‖ ≤ g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) ∧
      g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) ≤ (1 + ε) * ‖A v‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := inferInstance
  let B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun y ↦
    (g.inner (f y)).bilinearComp
      ((mfderiv (𝓡 n) (𝓡 n) f y).comp A.symm.toContinuousLinearMap)
      ((mfderiv (𝓡 n) (𝓡 n) f y).comp A.symm.toContinuousLinearMap)
  have hB : ContinuousAt B x := by
    apply continuousAt_clm_apply.mpr
    intro v
    apply continuousAt_clm_apply.mpr
    intro w
    exact (g.contDiffAt_pullback_inner hf (A.symm v) (A.symm w)).continuousAt
  have hnear : ∀ᶠ y in 𝓝 x, ‖B y - B x‖ < ε := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hB ε hε)
  filter_upwards [hnear] with y hy
  intro v
  have hself (z : EuclideanSpace ℝ (Fin n)) :
      B z (A v) (A v) =
        g.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 n) f z v) ^ 2 := by
    change g.inner (f z) (mfderiv (𝓡 n) (𝓡 n) f z (A.symm (A v)))
      (mfderiv (𝓡 n) (𝓡 n) f z (A.symm (A v))) = _
    rw [A.symm_apply_apply]
    unfold tangentNorm
    symm
    apply Real.sq_sqrt
    by_cases hz : mfderiv (𝓡 n) (𝓡 n) f z v = 0
    · simp [hz]
    · exact (g.pos (f z) _ hz).le
  have hcenter : B x (A v) (A v) = ‖A v‖ ^ 2 := by
    rw [hself, ← hA]
  have hclose : |g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) ^ 2 -
      ‖A v‖ ^ 2| ≤ ε * ‖A v‖ ^ 2 := by
    have h := (B y - B x).le_opNorm₂ (A v) (A v)
    simp only [sub_apply, Real.norm_eq_abs, hcenter, hself] at h
    calc
      _ ≤ ‖B y - B x‖ * ‖A v‖ * ‖A v‖ := h
      _ ≤ ε * ‖A v‖ ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy.le) (sq_nonneg ‖A v‖)]
  have hlo := (abs_le.mp hclose).1
  have hup := (abs_le.mp hclose).2
  have hnonneg : 0 ≤ g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) :=
    Real.sqrt_nonneg _
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (sub_nonneg.mpr hε₁) (norm_nonneg _)) hnonneg).mp
    nlinarith [mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hε₁)) (sq_nonneg ‖A v‖)]
  · apply (sq_le_sq₀ hnonneg (mul_nonneg (by linarith) (norm_nonneg _))).mp
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖A v‖),
      mul_nonneg hε.le (sq_nonneg ‖A v‖)]

theorem eventually_pullbackNorm_comparison (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ v, ‖A v‖ = g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v))
    {K : ℝ≥0} (hK : 1 < K) :
    ∀ᶠ y in 𝓝 x, ∀ v : EuclideanSpace ℝ (Fin n),
      ‖A v‖ ≤ (K : ℝ) * g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) ∧
      g.tangentNorm (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) ≤ (K : ℝ) * ‖A v‖ := by
  have hK' : 1 < (K : ℝ) := hK
  have hK0 : 0 < (K : ℝ) := lt_trans zero_lt_one hK'
  let ε : ℝ := 1 - (K : ℝ)⁻¹
  have hε : 0 < ε := sub_pos.mpr ((inv_lt_one₀ hK0).mpr hK')
  have hε₁ : ε ≤ 1 := sub_le_self _ (inv_nonneg.mpr hK0.le)
  have hcancel : (K : ℝ) * (1 - ε) = 1 := by
    dsimp [ε]
    rw [sub_sub_cancel, mul_inv_cancel₀ hK0.ne']
  have hupper : 1 + ε ≤ (K : ℝ) := by
    have h := sq_nonneg ((K : ℝ) - 1)
    have hinv : (K : ℝ) * (K : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hK0.ne'
    dsimp [ε]
    nlinarith
  filter_upwards [g.eventually_pullbackNorm_bounds hf A hA hε hε₁] with y hy
  intro v
  constructor
  · have h := mul_le_mul_of_nonneg_left (hy v).1 hK0.le
    simpa only [← mul_assoc, hcancel, one_mul] using h
  · exact (hy v).2.trans (mul_le_mul_of_nonneg_right hupper (norm_nonneg _))

end PoincareConjecture.RiemannianMetric
