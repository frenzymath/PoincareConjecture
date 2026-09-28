import PoincareConjecture.Proofs.M34.Standard.CapIsometryPullback
import PoincareConjecture.Proofs.M34.Standard.CapIsometryScalar
import PoincareConjecture.Proofs.M34.Standard.CapNeckImageIdentities

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X] [T2Space X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}

theorem exists_isometric_image (N : EpsilonNeck g)
    (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1)
    (D : LeviCivitaData h) :
    ∃ E : EpsilonNeck h, E.epsilon = N.epsilon ∧ E.scale = N.scale ∧
      E.center = f N.center ∧ E.connection = D ∧ E.carrier = f '' N.carrier ∧
      E.central_sphere = f '' N.central_sphere ∧
      ∀ a b : ℝ, -N.epsilon⁻¹ ≤ a → b ≤ N.epsilon⁻¹ →
        E.region a b = f '' N.region a b := by
  have hc : N.center ∈ N.coordinate_map '' (univ ×ˢ ({0} : Set ℝ)) := by
    rw [← N.central_sphere_eq]
    exact N.center_on_central_sphere
  obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hcenter⟩ := hc
  have hs0 : s = 0 := hs
  subst s
  let e := f.toHomeomorph.toOpenPartialHomeomorph
  have he : (e : M → X) = f := rfl
  have hdom : Ioo (-N.epsilon⁻¹ + (0 : ℝ)) (N.epsilon⁻¹ + 0) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by simp only [add_zero, Subset.rfl]
  have hsource : N.region (-N.epsilon⁻¹ + (0 : ℝ)) (N.epsilon⁻¹ + 0) ⊆
      e.source := subset_univ _
  have hscalar : 0 < D.scalarCurvature (e (N.coordinate_map (q, 0))) := by
    change 0 < D.scalarCurvature (f (N.coordinate_map (q, 0)))
    rw [M34.metricIsometry_scalar f hf N.connection D, hcenter]
    exact N.scalar_center_pos
  have hscale : N.scale = D.scalarCurvature (e (N.coordinate_map (q, 0))) ^
      (-1 / 2 : ℝ) := by
    change N.scale = D.scalarCurvature (f (N.coordinate_map (q, 0))) ^ (-1 / 2 : ℝ)
    rw [M34.metricIsometry_scalar f hf N.connection D, hcenter]
    exact N.scale_eq_scalar
  have hclose : RoundCylinderClose N.epsilon 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback h (fun z => e (N.coordinate_map (z.1, z.2 + 0))) z v w) := by
    simpa only [he, add_zero, Prod.mk.eta, Function.comp_def] using
      N.metricIsometry_comparison f hf
  let E := N.imageShift e f.contMDiff.contMDiffOn f.symm.contMDiff.contMDiffOn
    N.epsilon_pos N.epsilon_lt_half hdom hsource D q N.scale_pos hscalar hscale hclose
  have hsets := N.imageShift_zero_sets e f.contMDiff.contMDiffOn
    f.symm.contMDiff.contMDiffOn N.epsilon_pos N.epsilon_lt_half hdom hsource
    D q N.scale_pos hscalar hscale hclose rfl rfl
  refine ⟨E, rfl, rfl, ?_, rfl, hsets.1, hsets.2, ?_⟩
  · exact congrArg f hcenter
  · intro a b ha hb
    simpa only [he, add_zero] using N.imageShift_region e f.contMDiff.contMDiffOn
      f.symm.contMDiff.contMDiffOn N.epsilon_pos N.epsilon_lt_half hdom hsource
      D q N.scale_pos hscalar hscale hclose a b ha hb

end PoincareConjecture.EpsilonNeck
