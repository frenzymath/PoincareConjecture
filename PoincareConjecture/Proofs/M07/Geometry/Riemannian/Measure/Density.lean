import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Pullback
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Matrix

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


noncomputable def pullbackVolumeDensity (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (Matrix.of (fun i j : Fin n => g.inner (f x)
    (mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ j)))).det


theorem contDiffAt_pullbackVolumeDensity (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    ContDiffAt ℝ ∞ (g.pullbackVolumeDensity f) x ∧
      0 < g.pullbackVolumeDensity f x := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let G := fun y ↦ Matrix.of (fun i j : Fin n => g.inner (f y)
    (mfderiv (𝓡 n) (𝓡 n) f y (b i)) (mfderiv (𝓡 n) (𝓡 n) f y (b j)))
  have hpos : 0 < (G x).det := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change 0 < (Matrix.gram ℝ (fun i ↦ mfderiv (𝓡 n) (𝓡 n) f x (b i))).det
    apply Matrix.PosDef.det_pos
    apply Matrix.posDef_gram_of_linearIndependent
    exact b.toBasis.linearIndependent.map'
      (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap (LinearMap.ker_eq_bot.mpr hi)
  have hdet : ContDiffAt ℝ ∞ (fun y ↦ (G y).det) x := by
    have heq : (fun y ↦ (G y).det) = fun y ↦
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * ∏ i, G y (σ i) i := by
      funext y
      simp [Matrix.det_apply, Units.smul_def]
    rw [heq]
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    exact contDiffAt_prod (fun i _ ↦ g.contDiffAt_pullback_inner hf (b (σ i)) (b i))
  exact ⟨(Real.contDiffAt_sqrt hpos.ne').comp x hdet, Real.sqrt_pos.mpr hpos⟩


theorem contDiffAt_chartVolumeDensity (g : RiemannianMetric n M) (p : M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) p).target) :
    ContDiffAt ℝ ∞ (g.pullbackVolumeDensity (extChartAt (𝓡 n) p).symm) x ∧
      0 < g.pullbackVolumeDensity (extChartAt (𝓡 n) p).symm x := by
  apply g.contDiffAt_pullbackVolumeDensity
  · simpa only [modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ] using
      contMDiffWithinAt_extChartAt_symm_range (I := 𝓡 n) (n := ∞) p hx
  · simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm hx).injective

set_option backward.isDefEq.respectTransparency false in

theorem pullbackVolumeDensity_comp (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {e : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f (e x))
    (he : DifferentiableAt ℝ e x) :
    g.pullbackVolumeDensity (f ∘ e) x =
      |(fderiv ℝ e x).det| * g.pullbackVolumeDensity f (e x) := by
  classical
  have hchain (v : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) (f ∘ e) x v =
        mfderiv (𝓡 n) (𝓡 n) f (e x) (fderiv ℝ e x v) := by
    have h := mfderiv_comp_apply x hf he.mdifferentiableAt v
    rw [mfderiv_eq_fderiv] at h
    convert! h using 1
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let A := (mfderiv (𝓡 n) (𝓡 n) f (e x)).toLinearMap
  let T := (fderiv ℝ e x).toLinearMap
  let B := (g.inner (f (e x))).toBilinForm.comp A A
  have hB : Matrix.of (fun i j : Fin n => g.inner (f (e x))
      (mfderiv (𝓡 n) (𝓡 n) f (e x) (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) f (e x) (EuclideanSpace.basisFun (Fin n) ℝ j))) =
      (LinearMap.BilinForm.toMatrix b) B := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  have hBT : Matrix.of (fun i j : Fin n => g.inner ((f ∘ e) x)
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ e) x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ e) x (EuclideanSpace.basisFun (Fin n) ℝ j))) =
      (LinearMap.BilinForm.toMatrix b) (B.comp T T) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    dsimp only [Matrix.of_apply]
    erw [hchain, hchain]
    rfl
  unfold pullbackVolumeDensity
  rw [hB, hBT]
  change Real.sqrt ((LinearMap.BilinForm.toMatrix b) (B.comp T T)).det =
    |LinearMap.det T| * Real.sqrt ((LinearMap.BilinForm.toMatrix b) B).det
  rw [LinearMap.BilinForm.toMatrix_comp b b, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, LinearMap.det_toMatrix]
  rw [show LinearMap.det T * ((LinearMap.BilinForm.toMatrix b) B).det *
      LinearMap.det T = (LinearMap.det T) ^ 2 *
        ((LinearMap.BilinForm.toMatrix b) B).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

end PoincareConjecture.RiemannianMetric
