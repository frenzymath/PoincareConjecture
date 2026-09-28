import PoincareConjecture.Proofs.M76.Mathlib.PolygonProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates










set_option autoImplicit false

open Set Geometry

namespace Polygon




theorem closed_inside_axis_contact {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) :
    closure P.inside ∩ {z : ℝ × ℝ | z.2 = 0} =
      P.boundary ℝ ∩ {z : ℝ × ℝ | z.2 = 0} := by
  have hsub : closure P.inside ⊆ (univ : Set ℝ) ×ˢ Ici (0 : ℝ) := by
    apply P.closure_inside_subset_convex hP hi
      ((convex_univ : Convex ℝ (univ : Set ℝ)).prod (convex_Ici (0 : ℝ)))
    rintro _ ⟨i, rfl⟩
    exact ⟨mem_univ _, hup i⟩
  ext z
  constructor
  · rintro ⟨hz, hz0⟩
    refine ⟨?_, hz0⟩
    rw [← P.frontier_inside hP hi, frontier]
    refine ⟨hz, ?_⟩
    intro hzint
    have hzi : z ∈ interior (closure P.inside) :=
      interior_mono subset_closure hzint
    have hstrict := interior_mono hsub hzi
    rw [interior_prod_eq, interior_univ, interior_Ici] at hstrict
    exact (lt_irrefl (0 : ℝ)) (hz0 ▸ hstrict.2)
  · rintro ⟨hz, hz0⟩
    exact ⟨frontier_subset_closure (P.frontier_inside hP hi ▸ hz), hz0⟩






theorem exists_returning_arc_bigon {m n : ℕ}
    (K : SimplicialComplex ℝ (ℝ × ℝ))
    (a : Fin (m + 4) → ℝ × ℝ) (b : Fin (n + 4) → ℝ × ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : a (Fin.last (m + 3)) = b 0)
    (hba : b (Fin.last (n + 3)) = a 0)
    (haK : ∀ i : Fin (m + 3), ({a i.castSucc, a i.succ} : Finset (ℝ × ℝ)) ∈ K.faces)
    (hbK : ∀ i : Fin (n + 3), ({b i.castSucc, b i.succ} : Finset (ℝ × ℝ)) ∈ K.faces)
    (hinter : pathCarrier a ∩ pathCarrier b ⊆ {a 0, b 0})
    (ha_up : ∀ z ∈ pathCarrier a, 0 ≤ z.2)
    (ha_axis : pathCarrier a ∩ {z : ℝ × ℝ | z.2 = 0} ⊆ {a 0, b 0})
    (hb_axis : ∀ z ∈ pathCarrier b, z.2 = 0)
    {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    (haC : pathCarrier a ⊆ C) (hbC : pathCarrier b ⊆ C) :
    ∃ D : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) D (pathCarrier a ∪ pathCarrier b) ∧
      D ⊆ C ∧ IsCompact D ∧
      D ∩ {z : ℝ × ℝ | z.2 = 0} = pathCarrier b := by
  classical
  let P := ofPaths a b
  have hP : P.HasSimplicialEdges := hasSimplicialEdges_ofPaths K a b hab hba haK hbK
  have hia : range a ⊆ pathCarrier a := by
    rintro _ ⟨i, rfl⟩
    exact vertex_mem_pathCarrier a i
  have hib : range b ⊆ pathCarrier b := by
    rintro _ ⟨i, rfl⟩
    exact vertex_mem_pathCarrier b i
  have hi : Function.Injective P := injective_ofPaths a b ha hb hab hba
    ((inter_subset_inter hia hib).trans hinter)
  have hPb : P.boundary ℝ = pathCarrier a ∪ pathCarrier b := boundary_ofPaths a b hab hba
  have hPC : range P ⊆ C := by
    rintro _ ⟨i, rfl⟩
    rcases hPb ▸ P.vertex_mem_boundary i with h | h
    · exact haC h
    · exact hbC h
  have hup : ∀ i, 0 ≤ (P i).2 := by
    intro i
    rcases hPb ▸ P.vertex_mem_boundary i with h | h
    · exact ha_up _ h
    · exact le_of_eq (hb_axis _ h).symm
  have hends : {a 0, b 0} ⊆ pathCarrier b := by
    rintro x (rfl | hx)
    · rw [← hba]
      exact vertex_mem_pathCarrier b (Fin.last (n + 3))
    · rw [show x = b 0 from hx]
      exact vertex_mem_pathCarrier b 0
  refine ⟨closure P.inside, ?_, P.closure_inside_subset_convex hP hi hC hPC,
    P.isCompact_closure_inside hP hi, ?_⟩
  · rw [← hPb]
    exact P.isFinitePLBallPair_closed_inside hP hi
  · rw [P.closed_inside_axis_contact hP hi hup, hPb]
    ext z
    constructor
    · rintro ⟨ha' | hb', hz⟩
      · exact hends (ha_axis ⟨ha', hz⟩)
      · exact hb'
    · intro hz
      exact ⟨Or.inr hz, hb_axis _ hz⟩

end Polygon
