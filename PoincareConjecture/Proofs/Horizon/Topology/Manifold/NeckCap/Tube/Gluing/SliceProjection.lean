import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.FrontierScale
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphProjection













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck




theorem exists_sphereSlice_projection_diffeomorph :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N N' : EpsilonNeck g),
        N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
        ∀ {a : ℝ}, a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
        (∀ q : UnitTwoSphere, N'.coordinate_map (q, a) ∈ N.carrier) →
        ∃ e : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
          ∀ q : UnitTwoSphere,
            e q = (N.coordinate_inverse (N'.coordinate_map (q, a))).1 := by
  obtain ⟨ε₁, hε₁, hsmall, hscalar⟩ :=
    exists_ambient_scalar_control_on_closure.{u} (α := 1 / 2) (by norm_num)
  obtain ⟨ε₂, hε₂, _, hricci⟩ := exists_ricci_quadratic_control.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε hε' a ha hmem
  let f : UnitTwoSphere → UnitTwoSphere :=
    fun q => (N.coordinate_inverse (N'.coordinate_map (q, a))).1
  have hscale : N'.scale ≤ 2 * N.scale := by
    let q : UnitTwoSphere := Classical.choice inferInstance
    let x := N'.coordinate_map (q, a)
    have hx : x ∈ N.carrier := hmem q
    have hx' : x ∈ N'.carrier := N'.coordinate_map_mem ⟨mem_univ _, ha⟩
    have hl := (abs_le.mp (hscalar N N.connection
      (hε.trans (min_le_left _ _)) x (subset_closure hx))).1
    have hu := (abs_le.mp (hscalar N' N.connection
      (hε'.trans (min_le_left _ _)) x (subset_closure hx'))).2
    have hl' : (1 / 2 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature x := by
      linarith
    have hu' : N'.scale ^ 2 * N.connection.scalarCurvature x ≤ (3 / 2 : ℝ) := by
      linarith
    have hcomp : N'.scale ^ 2 ≤ 3 * N.scale ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_left hl' (sq_nonneg N'.scale)
      have h₂ := mul_le_mul_of_nonneg_left hu' (sq_nonneg N.scale)
      nlinarith
    apply (sq_le_sq₀ N'.scale_pos.le (mul_nonneg zero_le_two N.scale_pos.le)).mp
    nlinarith [sq_nonneg N.scale]
  have hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f := by
    have hc : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : UnitTwoSphere => N.coordinate_inverse (N'.coordinate_map (q, a))) := by
      intro q
      exact (N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (hmem q))).comp q (N'.sphereSlice_contMDiff ha q)
    exact contMDiff_fst.comp hc
  have hlocal : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ f := by
    apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hf
    intro q
    exact N.sphereSlice_projection_mfderiv_bijective_of_ricci_error N.connection N' ha q
      (hmem q) hscale
      (hricci N N.connection (hε.trans (min_le_right _ _)))
      (hricci N' N.connection (hε'.trans (min_le_right _ _)))
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  have hcover := isLocalHomeomorph_iff_isCoveringMap.mp hlocal.isLocalHomeomorph
  have hbij := Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected hcover
  exact ⟨hlocal.diffeomorphOfBijective hbij, fun _ => rfl⟩

end PoincareConjecture.EpsilonNeck
