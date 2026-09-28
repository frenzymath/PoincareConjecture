import PoincareConjecture.Proofs.M34.Standard.CapIsometryPullback
import PoincareConjecture.Proofs.M34.Standard.CapNeckImageIdentities
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}



theorem partialIsometry_neck_comparison (N : EpsilonNeck g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hsource : N.carrier ⊆ f.source)
    (hmetric : ∀ x ∈ f.source, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w)) :
    RoundCylinderClose N.epsilon 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback h (f ∘ N.coordinate_map) z v w) := by
  apply N.metric_comparison.close.congr_cylinder
  intro z hz v w
  have hzsource : N.coordinate_map z ∈ f.source :=
    hsource (N.coordinatePartialDiffeomorph.map_source ⟨mem_univ _, hz⟩)
  have hNd := ((N.coordinate_map_smooth z ⟨mem_univ _, hz⟩).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have hfd := ((f.contMDiffOn _ hzsource).contMDiffAt
    (f.open_source.mem_nhds hzsource)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z hfd hNd
  congr 1
  simp only [roundCylinderPullback, hchain, ContinuousLinearMap.comp_apply, Function.comp_apply]
  exact hmetric _ hzsource _ _



theorem exists_partialIsometry_neck_image (N : EpsilonNeck g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hsource : N.carrier ⊆ f.source)
    (hmetric : ∀ x ∈ f.source, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w))
    (D : LeviCivitaData h) :
    ∃ E : EpsilonNeck h, E.epsilon = N.epsilon ∧ E.scale = N.scale ∧
      E.center = f N.center ∧ E.connection = D ∧ E.carrier = f '' N.carrier ∧
      E.central_sphere = f '' N.central_sphere ∧ E.coordinate_map = f ∘ N.coordinate_map ∧
      ∀ a b : ℝ, -N.epsilon⁻¹ ≤ a → b ≤ N.epsilon⁻¹ →
        E.region a b = f '' N.region a b := by
  have hcenterMem : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hscalarEq : N.connection.scalarCurvature N.center = D.scalarCurvature (f N.center) :=
    N.connection.scalarCurvature_eq_of_local_isometry D f.open_source f.contMDiffOn
      hmetric (hsource hcenterMem)
  have hc : N.center ∈ N.coordinate_map '' (univ ×ˢ ({0} : Set ℝ)) := by
    rw [← N.central_sphere_eq]
    exact N.center_on_central_sphere
  obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hcenter⟩ := hc
  have hs0 : s = 0 := hs
  subst s
  let ep := f.toOpenPartialHomeomorph
  have hep : (ep : M → X) = f := rfl
  have hdom : Ioo (-N.epsilon⁻¹ + (0 : ℝ)) (N.epsilon⁻¹ + 0) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by simp only [add_zero, Subset.rfl]
  have hregion : N.region (-N.epsilon⁻¹ + (0 : ℝ)) (N.epsilon⁻¹ + 0) ⊆ ep.source :=
    fun _ hx => hsource hx.1
  have hscalar : 0 < D.scalarCurvature (ep (N.coordinate_map (q, 0))) := by
    change 0 < D.scalarCurvature (f (N.coordinate_map (q, 0)))
    rw [hcenter, ← hscalarEq]
    exact N.scalar_center_pos
  have hscale : N.scale = D.scalarCurvature (ep (N.coordinate_map (q, 0))) ^
      (-1 / 2 : ℝ) := by
    change N.scale = D.scalarCurvature (f (N.coordinate_map (q, 0))) ^ (-1 / 2 : ℝ)
    rw [hcenter, ← hscalarEq]
    exact N.scale_eq_scalar
  have hclose : RoundCylinderClose N.epsilon 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback h (fun z => ep (N.coordinate_map (z.1, z.2 + 0))) z v w) := by
    simpa only [hep, add_zero, Prod.mk.eta, Function.comp_def] using
      partialIsometry_neck_comparison N f hsource hmetric
  let E := N.imageShift ep f.contMDiffOn f.symm.contMDiffOn
    N.epsilon_pos N.epsilon_lt_half hdom hregion D q N.scale_pos hscalar hscale hclose
  have hsets := N.imageShift_zero_sets ep f.contMDiffOn f.symm.contMDiffOn
    N.epsilon_pos N.epsilon_lt_half hdom hregion D q N.scale_pos hscalar hscale hclose rfl rfl
  refine ⟨E, rfl, rfl, congrArg f hcenter, rfl, hsets.1, hsets.2, ?_, ?_⟩
  · funext z
    change f (N.coordinate_map (z.1, z.2 + 0)) = (f ∘ N.coordinate_map) z
    simp only [add_zero, Prod.mk.eta, Function.comp_apply]
  · intro a b ha hb
    simpa only [hep, add_zero] using N.imageShift_region ep f.contMDiffOn f.symm.contMDiffOn
      N.epsilon_pos N.epsilon_lt_half hdom hregion D q N.scale_pos hscalar hscale hclose a b ha hb

end PoincareConjecture.Proofs.M47
