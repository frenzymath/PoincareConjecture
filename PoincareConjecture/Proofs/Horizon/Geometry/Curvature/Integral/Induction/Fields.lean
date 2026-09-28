import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.HypersurfaceFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem inner_levelUnitNormal_self (D : LeviCivitaData g)
    (f : M → ℝ) (x : M) (hx : 0 < D.levelQ f x) :
    g.inner x (D.levelUnitNormal f x) (D.levelUnitNormal f x) = 1 := by
  simp only [levelUnitNormal, map_smul, smul_apply, smul_eq_mul]
  change (Real.sqrt (D.levelQ f x))⁻¹ *
    ((Real.sqrt (D.levelQ f x))⁻¹ * D.levelQ f x) = 1
  have hs := Real.sq_sqrt hx.le
  have hn := (Real.sqrt_pos.mpr hx).ne'
  field_simp
  nlinarith

theorem ricci_levelUnitNormal_eq (D : LeviCivitaData g)
    (f : M → ℝ) (x : M) :
    D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) =
      D.ricci x (D.gradient f x) (D.gradient f x) / D.levelQ f x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hq : 0 ≤ D.levelQ f x := by
    change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
    exact real_inner_self_nonneg
  unfold levelUnitNormal ricci
  simp_rw [← D.curvatureTensor_bilinear_first_third_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hq]
  exact (div_eq_inv_mul _ _).symm

theorem continuousOn_ricci_levelUnitNormal (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn (fun x => D.ricci x (D.levelUnitNormal f x)
      (D.levelUnitNormal f x)) {x | 0 < D.levelQ f x} := by
  have hRic : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => D.ricci x (D.gradient f x) (D.gradient f x)) := by
    intro x
    exact D.ricciEvaluation_isSmooth_manifold.contMDiffAt_apply
      (X := fun _ => D.gradient f) (fun _ => D.contMDiffAt_gradient (hf x))
  have heq : (fun x => D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x)) =
      (fun x => D.ricci x (D.gradient f x) (D.gradient f x)) / D.levelQ f :=
    funext (D.ricci_levelUnitNormal_eq f)
  rw [heq]
  exact hRic.continuous.continuousOn.div
    (D.contMDiff_levelQ hf).continuous.continuousOn (fun x hx => ne_of_gt hx)

theorem continuousOn_levelGaussTerm (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn (D.levelGaussTerm f) {x | 0 < D.levelQ f x} := by
  have h := (D.continuousOn_levelBochnerDifference hf).add
    (D.continuousOn_ricci_levelUnitNormal hf)
  have heq : D.levelGaussTerm f = D.levelBochnerDifference f +
      (fun x => D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x)) := by
    funext x
    exact (sub_add_cancel _ _).symm
  rw [heq]
  exact h

end PoincareConjecture.LeviCivitaData
