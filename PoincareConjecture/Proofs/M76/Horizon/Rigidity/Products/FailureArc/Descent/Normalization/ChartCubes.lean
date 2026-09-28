import PoincareConjecture.Proofs.M76.Dehn.OriginalPairedRegionCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_marked_surface_chart_cube
    {s t : Stage e S f r C} (step : Step s t) {R : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) {W : Set M} (hW : IsOpen W)
    {x : t.Carrier} (hxR : x ∈ t.projection ⁻¹' R)
    (hxW : x ∈ frontier (t.projection ⁻¹' R) → t.projection x ∈ W) :
    ∃ (Q : OpenPartialHomeomorph t.Carrier V3)
      (B : OpenPartialHomeomorph s.Carrier V3)
      (a : ℝ) (J : SimplicialComplex ℝ V3),
      x ∈ Q.source ∧ InjOn (step.projection ∘ step.inclusion) Q.source ∧
      (∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ l, (s.charts l).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      Q.target = B.target ∧
      (∀ y, Q y = B (step.projection (step.inclusion y))) ∧
      MapsTo (step.projection ∘ step.inclusion) Q.source B.source ∧
      EqOn ((step.projection ∘ step.inclusion) ∘ Q.symm) B.symm B.target ∧
      0 < a ∧ J.faces.Finite ∧ J.space = closedBall (Q x) (3 * a) ∧
      J.space ⊆ Q.target ∧ closure (ball (Q x) a) ⊆ ball (Q x) (2 * a) ∧
      closure (ball (Q x) (2 * a)) ⊆ interior J.space ∧
      (x ∈ interior (t.projection ⁻¹' R) →
        Q.source ⊆ interior (t.projection ⁻¹' R)) ∧
      (x ∈ frontier (t.projection ⁻¹' R) → Q.source ⊆ t.projection ⁻¹' W) ∧
      (B.source ⊆ interior (s.projection ⁻¹' R) ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ell (Q x) = 0 ∧
          (∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y)) ∧
          ∀ y ∈ B.source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B y) = 0) := by
  classical
  let V : Set t.Carrier := if x ∈ interior (t.projection ⁻¹' R)
    then interior (t.projection ⁻¹' R) else t.projection ⁻¹' W
  have hV : IsOpen V := by
    dsimp only [V]
    split_ifs
    · exact isOpen_interior
    · exact hW.preimage t.projection.continuous
  have hxV : x ∈ V := by
    dsimp only [V]
    split_ifs with hx
    · exact hx
    · exact hxW ⟨subset_closure hxR, hx⟩
  obtain ⟨Q, B, hxQ, hQV, hinj, hQ, hB, htarget, hval, hmaps, hinv, hmodel⟩ :=
    step.exists_paired_original_region_charts he hxR hV hxV
  obtain ⟨a, J, ha, hJ, hJs, hJQ, hsmall, hlarge⟩ :=
    SimplicialComplex.exists_nested_finite_coordinate_cubes Q.open_target (Q.map_source hxQ)
  refine ⟨Q, B, a, J, hxQ, hinj, hQ, hB, htarget, hval, hmaps, hinv,
    ha, hJ, hJs, hJQ, hsmall, hlarge, ?_, ?_, hmodel⟩
  · intro hx
    simpa only [V, if_pos hx] using hQV
  · intro hx
    simpa only [V, if_neg hx.2] using hQV

end Geometry.OriginalPLTower
