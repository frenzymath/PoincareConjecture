import PoincareConjecture.Proofs.M76.Mathlib.DerivedVertexLinkFaces
import PoincareConjecture.Proofs.M76.Mathlib.OrderComplexMapImage

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

open PoincareConjecture.Proofs.M02.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

theorem derived_link_space_eq_flag_range {p : E} (hp : {p} ∈ K.faces)
    [Fintype (K.link p).faces] :
    ((K.derivedSubdivision c hc).link p).space =
      range (finiteOrderComplexMap (K.link p).faces
        (fun s => c ⟨insert p s.val, s.property.2.2⟩)) := by
  classical
  ext x
  rw [mem_range_finiteOrderComplexMap_iff]
  simp only [← Finset.coe_image]
  constructor
  · intro hx
    obtain ⟨f, hf, hxf⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha, hchain, rfl⟩ := (K.derivedSubdivision_link_faces c hc hp f).mp hf
    exact ⟨a, ha, hchain, hxf⟩
  · rintro ⟨a, ha, hchain, hx⟩
    exact convexHull_subset_space
      ((K.derivedSubdivision_link_faces c hc hp _).mpr ⟨a, ha, hchain, rfl⟩) hx

theorem isConnected_derived_original_vertex_link {p : E} (hp : {p} ∈ K.faces)
    (hconn : IsConnected (K.link p).space) :
    IsConnected ((K.derivedSubdivision c hc).link p).space := by
  classical
  let : Fintype (K.link p).faces :=
    (finite_link_faces (Set.toFinite K.faces) p).fintype
  let cL : (K.link p).faces → E := fun s => c ⟨s.val, s.property.1⟩
  have hcL : ∀ s : (K.link p).faces, ∃ w : E → ℝ,
      (∀ v ∈ s.val, 0 < w v) ∧ (∑ v ∈ s.val, w v) = 1 ∧
        (∑ v ∈ s.val, w v • v) = cL s := fun s => hc ⟨s.val, s.property.1⟩
  let : ConnectedSpace (finiteOrderComplex (K.link p).faces).space :=
    isConnected_iff_connectedSpace.mp
      ((K.link p).isConnected_faceOrderComplex cL hcL hconn)
  rw [K.derived_link_space_eq_flag_range c hc hp]
  exact isConnected_range (finiteOrderComplexMap (K.link p).faces _).continuous

end Geometry.SimplicialComplex
