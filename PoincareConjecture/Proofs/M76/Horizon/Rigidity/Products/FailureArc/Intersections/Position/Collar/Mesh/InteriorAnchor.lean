import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Frontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.RegionPreservation



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalSurfacePairChart.exists_interior_intersection_in_neighborhood
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R W : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hR : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (hW : IsOpen W) (hyW : y ∈ W) :
    ∃ p ∈ S ∩ T, p ∈ interior R ∩ W := by
  let Q := C.chart.trans C.coordinates
  have hyQ : y ∈ Q.source := ⟨C.center_source, C.center_coordinates⟩
  have hzeroQ : (0 : E3) ∈ Q.target := C.center_zero ▸ Q.map_source hyQ
  have hQzero : Q.symm 0 = y := by rw [← C.center_zero]; exact Q.left_inv hyQ
  let O := Q.target ∩ Q.symm ⁻¹' W
  have hO : IsOpen O := Q.symm.isOpen_inter_preimage hW
  have hzeroO : (0 : E3) ∈ O := ⟨hzeroQ, by change Q.symm 0 ∈ W; rwa [hQzero]⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO 0 hzeroO
  let v : E3 := ((0, r / 2), 0)
  have hvnorm : ‖v‖ = r / 2 := by
    simp only [v, Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_of_pos (half_pos hr),
      max_eq_right (half_pos hr).le, max_eq_left (half_pos hr).le]
  have hvO : v ∈ O := hrO (by
    rw [mem_ball_zero_iff, hvnorm]
    exact half_lt_self hr)
  have hvtarget : v ∈ C.coordinates.target := hvO.1.1
  have hz : C.coordinates.symm v ∈ C.coordinates.source := C.coordinates.map_target hvtarget
  have hcoord := C.coordinates.right_inv hvtarget
  have hS : Q.symm v ∈ S := (C.first_surface _ hz).mpr (by
    rw [hcoord]
    exact ⟨rfl, fun _ => (half_pos hr).le⟩)
  have hT : Q.symm v ∈ T := (C.second_surface _ hz).mpr (by
    rw [hcoord]
    exact ⟨rfl, fun _ => (half_pos hr).le⟩)
  have hpR : Q.symm v ∈ R := (hR _ hz).mpr (by rw [hcoord]; exact (half_pos hr).le)
  have hpfront : Q.symm v ∉ frontier R := by
    intro hp
    have hh := (C.frontier_iff_of_region_halfspace hR _ hz).mp hp
    rw [hcoord] at hh
    exact (half_pos hr).ne' hh
  refine ⟨Q.symm v, ⟨hS, hT⟩, ?_, hvO.2⟩
  by_contra hn
  exact hpfront ⟨subset_closure hpR, hn⟩

theorem proper_map_preserved_of_fixed_boundary_pair
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    {Source rim : Set E} {T R W : Set X} {f : E → X} {y : X}
    (hf : ContinuousOn f Source) (hmap : MapsTo f Source R)
    (hproper : ∀ x ∈ Source, f x ∈ frontier R ↔ x ∈ rim)
    (hconnected : IsPreconnected (Source \ rim))
    (C : OriginalSurfacePairChart e (f '' Source) T y true)
    (hR : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (F : X ≃ₜ X) (hfrontier : EqOn F id (frontier R))
    (hW : IsOpen W) (hyW : y ∈ W) (hfix : EqOn F id W) :
    MapsTo (F ∘ f) Source R ∧
      (∀ x ∈ Source, (F ∘ f) x ∈ frontier R ↔ x ∈ rim) ∧
      EqOn (F ∘ f) f (Source ∩ rim) ∧
      MapsTo (F ∘ f) (Source \ rim) (interior R) := by
  obtain ⟨p, ⟨hpS, _⟩, hpR, hpW⟩ := C.exists_interior_intersection_in_neighborhood hR hW hyW
  obtain ⟨a, ha, rfl⟩ := hpS
  have harim : a ∉ rim := by
    intro h
    exact disjoint_left.mp disjoint_interior_frontier hpR ((hproper a ha).mpr h)
  exact proper_map_preserved_of_fixed_frontier_and_anchor hf hmap hproper hconnected F
    hfrontier ⟨ha, harim⟩ (hfix hpW)

end PoincareConjecture.M76
