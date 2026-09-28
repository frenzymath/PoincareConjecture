import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Cap.Geometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive.SoulCapGeometry

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {delta D R epsilon : ℝ}
  {G : SoulNeckRegion K S delta D R} (H : SoulCapGeometry G epsilon)

theorem closed_core_eq_complement_end :
    closure G.inside = H.carrier \ H.endNeck.carrier := by
  rw [H.end_carrier]
  exact (G.bufferedCarrier_diff_region H.source H.source_sphere H.source_height
    H.outer_height_pos).symm

theorem boundary_eq_end_frontier :
    H.source.central_sphere = H.carrier ∩ frontier H.endNeck.carrier := by
  rw [H.end_carrier]
  exact (G.bufferedCarrier_inter_frontier_region H.source H.source_sphere
    H.source_height H.outer_height_pos H.outer_height_lt).symm

theorem boundary_sphere_subset : H.source.central_sphere ⊆ H.carrier := by
  rw [H.boundary_eq_end_frontier]
  exact inter_subset_left

theorem core_frontier_eq_boundary : frontier (closure G.inside) = H.source.central_sphere :=
  G.frontier_closure_inside.trans H.source_sphere.symm

theorem core_eq_interior_closed_core : G.inside = interior (closure G.inside) :=
  G.interior_closure_inside.symm

theorem boundary_local_defining_function {x : M} (hx : x ∈ H.source.central_sphere) :
    ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ U ⊆ H.carrier ∧
        (∀ y ∈ U, y ∈ closure G.inside ↔ f y ≤ 0) ∧ f x = 0 ∧
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
        ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) f x d ≠ 0 :=
  G.buffered_boundary_local_defining_function H.source H.source_height H.outer_height_pos hx

theorem negative_end_region :
    H.endNeck.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) =
      H.source.region 0 (H.a * epsilon⁻¹ / 2) := by
  have ha : 0 < H.a := by linarith [H.a_bounds.1]
  have hscale : 0 < H.a * epsilon⁻¹ := mul_pos ha (inv_pos.mpr H.epsilon_pos)
  ext x
  change (x ∈ H.endNeck.carrier ∧
      -epsilon⁻¹ < (H.endNeck.coordinate_inverse x).2 ∧
      (H.endNeck.coordinate_inverse x).2 < -epsilon⁻¹ / 2) ↔
    (x ∈ H.source.carrier ∧ 0 < (H.source.coordinate_inverse x).2 ∧
      (H.source.coordinate_inverse x).2 < H.a * epsilon⁻¹ / 2)
  rw [H.end_carrier, H.end_coordinate_inverse]
  dsimp only [Function.comp_apply, RoundCylinderAffine.inverseSpace]
  constructor
  · rintro ⟨⟨hx, hlo, _⟩, _, hhi⟩
    refine ⟨hx, hlo, ?_⟩
    have h := (div_lt_iff₀ ha).mp hhi
    nlinarith
  · rintro ⟨hx, hlo, hhi⟩
    refine ⟨⟨hx, hlo, ?_⟩, ?_, ?_⟩
    · nlinarith
    · apply (lt_div_iff₀ ha).mpr
      nlinarith
    · apply (div_lt_iff₀ ha).mpr
      nlinarith

theorem boundary_subset_negative_end_closure : H.source.central_sphere ⊆
    closure (H.endNeck.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
  rw [H.negative_end_region]
  have ha : 0 < H.a := by linarith [H.a_bounds.1]
  have ht : 0 < H.a * epsilon⁻¹ / 2 :=
    div_pos (mul_pos ha (inv_pos.mpr H.epsilon_pos)) (by norm_num)
  intro x hx
  obtain ⟨hxN, hzero⟩ := (H.source.mem_central_sphere_iff x).mp hx
  apply (H.source.mem_closure_region_iff_of_mem_carrier ht hxN).mpr
  rw [hzero]
  exact ⟨le_rfl, ht.le⟩

end PoincareConjecture.NoncompactKappa.Positive.SoulCapGeometry
