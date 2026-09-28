import PoincareConjecture.Proofs.M76.Dehn.OriginalPairedRegionCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}

structure RelativeChartBox (step : Step s t) (R : Set M) (x : t.Carrier) where
  upper : OpenPartialHomeomorph t.Carrier V3
  lower : OpenPartialHomeomorph s.Carrier V3
  radius : ℝ
  support : SimplicialComplex ℝ V3
  point : x ∈ upper.source
  projection_injective : InjOn (step.projection ∘ step.inclusion) upper.source
  upper_compatible : ∀ k, (t.charts k).symm.trans upper ∈ piecewiseAffineGroupoid V3
  lower_compatible : ∀ k, (s.charts k).symm.trans lower ∈ piecewiseAffineGroupoid V3
  targets : upper.target = lower.target
  projection_value : ∀ y, upper y = lower (step.projection (step.inclusion y))
  projection_maps : MapsTo (step.projection ∘ step.inclusion) upper.source lower.source
  projection_inverse : EqOn ((step.projection ∘ step.inclusion) ∘ upper.symm)
    lower.symm lower.target
  radius_pos : 0 < radius
  finite_support : support.faces.Finite
  support_space : support.space = closedBall (upper x) (3 * radius)
  support_target : support.space ⊆ upper.target
  small_large : closure (ball (upper x) radius) ⊆ ball (upper x) (2 * radius)
  large_support : closure (ball (upper x) (2 * radius)) ⊆ interior support.space
  interior_source : x ∈ interior (t.projection ⁻¹' R) →
    upper.source ⊆ interior (t.projection ⁻¹' R)

theorem Step.nonempty_relative_chart_box (step : Step s t) {R : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) {x : t.Carrier}
    (hxR : x ∈ t.projection ⁻¹' R) : Nonempty (RelativeChartBox step R x) := by
  classical
  let W : Set t.Carrier := if x ∈ interior (t.projection ⁻¹' R)
    then interior (t.projection ⁻¹' R) else univ
  have hW : IsOpen W := by
    dsimp only [W]
    split_ifs
    · exact isOpen_interior
    · exact isOpen_univ
  have hxW : x ∈ W := by
    dsimp only [W]
    split_ifs with hx
    · exact hx
    · exact mem_univ x
  obtain ⟨Q, B, hxQ, hQW, hinj, hQ, hB, htarget, hval, hmaps, hinv, _⟩ :=
    step.exists_paired_original_region_charts he hxR hW hxW
  obtain ⟨a, J, ha, hJ, hJs, hJQ, hsmall, hlarge⟩ :=
    SimplicialComplex.exists_nested_finite_coordinate_cubes Q.open_target (Q.map_source hxQ)
  refine ⟨⟨Q, B, a, J, hxQ, hinj, hQ, hB, htarget, hval, hmaps, hinv,
    ha, hJ, hJs, hJQ, hsmall, hlarge, ?_⟩⟩
  intro hx
  simpa only [W, if_pos hx] using hQW

namespace RelativeChartBox

variable {step : Step s t} {R : Set M} {x : t.Carrier}

def neighborhood (b : RelativeChartBox step R x) : Set t.Carrier :=
  b.upper.source ∩ b.upper ⁻¹' ball (b.upper x) (2 * b.radius)

theorem neighborhood_open (b : RelativeChartBox step R x) : IsOpen b.neighborhood :=
  b.upper.continuousOn.isOpen_inter_preimage b.upper.open_source isOpen_ball

theorem neighborhood_injective (b : RelativeChartBox step R x) :
    InjOn (step.projection ∘ step.inclusion) b.neighborhood :=
  b.projection_injective.mono inter_subset_left

theorem neighborhood_support (b : RelativeChartBox step R x) :
    b.neighborhood ⊆ b.upper.source ∩ b.upper ⁻¹' interior b.support.space :=
  fun _ hy ↦ ⟨hy.1, b.large_support (subset_closure hy.2)⟩

theorem convex_support (b : RelativeChartBox step R x) : Convex ℝ b.support.space := by
  rw [b.support_space]
  exact convex_closedBall _ _

end RelativeChartBox
end Geometry.OriginalPLTower
