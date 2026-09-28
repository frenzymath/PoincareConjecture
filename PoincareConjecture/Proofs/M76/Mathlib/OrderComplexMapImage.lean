import PoincareConjecture.Proofs.M76.Mathlib.DerivedSubdivision

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

open PoincareConjecture.Proofs.M02.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

include hc in

theorem range_faceOrderComplexMap :
    range (finiteOrderComplexMap K.faces c) = K.space := by
  classical
  rw [← K.derivedSubdivision_space c hc]
  ext x
  rw [mem_range_finiteOrderComplexMap_iff]
  simp only [← Finset.coe_image]
  constructor
  · rintro ⟨a, ha, hchain, hx⟩
    exact convexHull_subset_space
      ((K.derivedSubdivision_faces c hc _).mpr ⟨a, ha, hchain, rfl⟩) hx
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha, hchain, rfl⟩ := (K.derivedSubdivision_faces c hc s).mp hs
    exact ⟨a, ha, hchain, hxs⟩

include c hc in

theorem isConnected_faceOrderComplex (hconn : IsConnected K.space) :
    IsConnected (finiteOrderComplex K.faces).space := by
  let e := geometricFlagHomeomorphRange K Subtype.val (fun s => s.property)
    (fun _ _ => Iff.rfl) c hc
  have hconn' : IsConnected (range (finiteOrderComplexMap K.faces c)) := by
    rwa [K.range_faceOrderComplexMap c hc]
  exact isConnected_iff_connectedSpace.mpr
    (e.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp hconn'))

end Geometry.SimplicialComplex
