import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.ClosedExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexRadialNormalization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralIntersections
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.FinitePLUnionMaps

/-!
# Finite PL extension by the identity outside a polyhedral body

Intersect any finite ambient carrier with the body and with
each closed exterior halfspace. On exterior pieces the closed
extension is exactly the identity, including their frontier
overlap. Finite PL pasting certifies the whole original carrier.
See Hamilton 1976, pp. 66--68, Hudson 1969, pp. 12--19 and
M76 derivation 248.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

/-- Extending a frontier-fixed homeomorphism by the identity
fixes every point outside the interior of its closed domain.
See Hamilton pp. 66--68 and M76 derivation 248. -/
theorem closedExtension_apply_notMem_interior
    {X : Type*} [TopologicalSpace X] {C : Set X} (e : C ≃ₜ C)
    (hC : IsClosed C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x)
    {x : X} (hx : x ∉ interior C) : e.closedExtension hC hfix x = x := by
  by_cases hxC : x ∈ C
  · exact e.closedExtension_apply_frontier hC hfix ⟨subset_closure hxC, hx⟩
  · exact e.closedExtension_apply_notMem hC hfix hxC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A frontier-fixed finite PL homeomorphism of an actual
finite unit-halfspace body extends by the identity to a map
finite PL on every finite ambient carrier. All exterior
pieces and the complete carrier cover are constructed from
the halfspace description. See Hudson pp. 12--19, Hamilton
pp. 66--68 and M76 derivation 248. -/
theorem IsFinitePL.closedExtension_finitePiecewiseAffineOn
    {C : Set E} {e : C ≃ₜ C} (he : e.IsFinitePL) (hC : IsClosed C)
    (hfix : ∀ x : C, (x : E) ∈ frontier C → e x = x)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (hrep : C = {x | ∀ i, L i x ≤ 1})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) :
    FinitePiecewiseAffineOn (e.closedExtension hC hfix : E → E) J.space := by
  classical
  let G := e.closedExtension hC hfix
  obtain ⟨f, hf, hef⟩ := he
  have hGC : FinitePiecewiseAffineOn (G : E → E) C :=
    hf.congr (fun x hx => (hef ⟨x, hx⟩).symm.trans
      (e.closedExtension_apply_mem hC hfix hx).symm)
  obtain ⟨K, hK, hKs, _⟩ := hf
  obtain ⟨R, hR, hRs⟩ := J.exists_finite_triangulation_inter K hJ hK
  rw [hKs] at hRs
  have hinside : FinitePiecewiseAffineOn (G : E → E) (J.space ∩ C) := by
    rw [← hRs]
    exact hGC.restrict R hR (hRs.subset.trans inter_subset_right)
  have hGoutside (i : ι) (x : E) (hx : 1 ≤ L i x) : G x = x := by
    by_cases hxC : x ∈ C
    · have hbound : ∀ j, L j x ≤ 1 := by
        have hm : x ∈ {y | ∀ j, L j y ≤ 1} := hrep ▸ hxC
        exact hm
      have hxfront : x ∈ frontier C := by
        rw [hrep, frontier_finite_linear_unit_halfspaces L hL]
        exact ⟨hbound, i, (hbound i).antisymm hx⟩
      exact e.closedExtension_apply_frontier hC hfix hxfront
    · exact e.closedExtension_apply_notMem hC hfix hxC
  have hpieces (i : ι) :
      FinitePiecewiseAffineOn (G : E → E) (J.space ∩ {x | 1 ≤ L i x}) := by
    let A : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1 - (L i).toAffineMap
    obtain ⟨T, hT, hTs⟩ := J.exists_finite_triangulation_inter_halfspaces hJ {A}
    have hTA : {x | ∀ a ∈ ({A} : Finset (E →ᵃ[ℝ] ℝ)), a x ≤ 0} =
        {x | 1 ≤ L i x} := by
      ext x
      simp only [Finset.mem_singleton, forall_eq, A, AffineMap.coe_sub,
        Pi.sub_apply, AffineMap.const_apply, LinearMap.coe_toAffineMap, sub_nonpos]
    rw [hTA] at hTs
    have hid := (T.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).finitePiecewiseAffineOn hT
    rw [hTs] at hid
    exact hid.congr (fun x hx => (hGoutside i x hx.2).symm)
  have hcover : (J.space ∩ C) ∪ (⋃ i, J.space ∩ {x | 1 ≤ L i x}) = J.space := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact hx.1
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact hi.1
    · intro x hx
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hx, hxC⟩
      · have hn : ¬ ∀ i, L i x ≤ 1 := by
          intro h
          apply hxC
          rw [hrep]
          exact h
        push Not at hn
        obtain ⟨i, hi⟩ := hn
        exact Or.inr (mem_iUnion.mpr ⟨i, hx, hi.le⟩)
  have htotal := finitePiecewiseAffineOn_union hinside (FinitePiecewiseAffineOn.iUnion hpieces)
  rwa [hcover] at htotal

end Homeomorph
