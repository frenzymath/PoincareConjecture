import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalRegion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Orientation.LocalProjection
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Geometry AbstractSimplicialComplex
open PoincareConjecture.M76
open Poincare.Topology.Orientation.ProjectivePlane
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

theorem exists_three_chart_labels_of_localOrientation
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X) {ι : Type*}
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) :
    ∃ label : ∀ i, LocallyConstant (e i).source PLOrientationSheet,
      ∀ i j (x : X) (hi : x ∈ (e i).source) (hj : x ∈ (e j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign e he i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let a : (Fin 3 → ℝ) ≃ᴬ[ℝ] E3 :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousAffineEquiv
  let q (i : ι) := (e i).transHomeomorph a.toHomeomorph
  have hq := affine_model_plAtlas_compatible e he a
  obtain ⟨label, hlabel⟩ := exists_plAtlas_labels_of_localOrientation
    O euclideanLocalOrientation q hq
  refine ⟨label, ?_⟩
  intro i j x hi hj
  have h := hlabel i j x hi hj
  rw [plAtlasTransitionSign_affine_model e he a i j ⟨x, hi, hj⟩] at h
  exact h

end PoincareConjecture.M76

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem MarkedTerminalRegion.exists_boundary_signs_of_localOrientation
    {X ι : Type} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → X}
    {r : X → ℝ} {C R : Set X} {st : Stage e S f r C}
    (N : MarkedTerminalRegion st R) (O : LocalOrientation st.Carrier) :
    ∃ (number : (N.sample → ℝ × V3) → ℕ)
      (sign : Finset (N.sample → ℝ × V3) → ZMod 2),
      InjOn number N.boundary.vertices ∧
      ∀ t ∈ N.boundary.faces, t.card = 3 →
        ∀ u ∈ N.boundary.faces, u.card = 3 → t ≠ u →
          ∀ s : Finset (N.sample → ℝ × V3), s.card = 2 → s ⊆ t → s ⊆ u →
            (sign t + boundaryFaceParity number t s) +
              (sign u + boundaryFaceParity number u s) = 1 := by
  classical
  let E := N.sample → ℝ × V3
  let g : E → st.Carrier := fun z => N.inverse z
  have hgi : InjOn g N.complex.space := by
    intro x hx y hy hxy
    have h : N.homeomorph.symm ⟨x, hx⟩ = N.homeomorph.symm ⟨y, hy⟩ :=
      Subtype.ext ((N.inverse_value ⟨x, hx⟩).symm.trans
        (hxy.trans (N.inverse_value ⟨y, hy⟩)))
    exact congrArg Subtype.val (N.homeomorph.symm.injective h)
  have hg : ContinuousOn g N.boundary.space :=
    N.inverse_PL.continuousOn.mono (SimplicialComplex.space_subset_of_le N.boundary_le)
  have hfront : MapsTo g N.boundary.space (frontier N.region) := by
    intro z hz
    apply (original_model_mem_image_iff N.homeomorph N.graph N.inverse
      N.homeomorph_value N.inverse_value N.domain.closed.frontier_subset
      ⟨z, SimplicialComplex.space_subset_of_le N.boundary_le hz⟩).mpr
    exact N.boundary_image ▸ hz
  let charts := {D : OpenPartialHomeomorph st.Carrier V3 |
    ∀ i, (st.charts i).symm.trans D ∈ piecewiseAffineGroupoid V3}
  let q : charts → OpenPartialHomeomorph st.Carrier V3 := Subtype.val
  have hq : ∀ H D, (q H).symm.trans (q D) ∈ piecewiseAffineGroupoid V3 :=
    fun H D => compatiblePLCharts_trans st.charts st.cover st.compatible
      H D H.property D.property
  obtain ⟨label, hlabel⟩ := exists_three_chart_labels_of_localOrientation O q hq
  let pull (H : charts) : C({z : N.boundary.space | g z ∈ H.val.source}, H.val.source) :=
    ⟨fun z => ⟨g z.val, z.property⟩,
      (hg.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        (fun z => z.val.property)).subtype_mk _⟩
  let labels (H : charts) := LocallyConstant.comap (pull H) (label H)
  have hstars : ∀ p ∈ N.complex.vertices, ∃ D : OpenPartialHomeomorph st.Carrier V3,
      (∀ i, (st.charts i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (N.complex.closedStar p).space D.source ∧
      (N.complex.closedStar p).AffineOnFaces (D ∘ g) ∧
      (D.source ⊆ N.region ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ D.source, y ∈ N.region ↔ 0 ≤ ell (D y)) := by
    intro p hp
    obtain ⟨D, hD, hcompat, hAff, hreg⟩ := N.stars p hp
    exact ⟨D, hcompat, hD, hAff, hreg⟩
  obtain ⟨number, sign, hsign⟩ :=
    exists_frontier_all_edge_signs_of_chart_labels st.charts N.complex N.boundary
      N.boundary_le (N.finite.subset N.boundary_le) g N.region hgi hfront hstars
      hq labels (fun H D z hH hD => hlabel H D (g z) hH hD)
  exact Dehn.exists_geometric_coface_signs N.boundary number sign hsign

end Geometry.OriginalPLTower
