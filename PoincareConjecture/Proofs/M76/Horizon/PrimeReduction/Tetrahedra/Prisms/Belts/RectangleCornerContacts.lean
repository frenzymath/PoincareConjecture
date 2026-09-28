import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.RectangleOriginalEdges



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem OriginalFaceRectangles.cap_inter_side_nonempty
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (k : D.Region) (a b : Bool) :
    (D.arc (D.cap k a) ∩ D.side k b).Nonempty := by
  obtain ⟨G,_,hW,hZ,hL,hR⟩ := D.rectangle k
  let x : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    ⟨(if b then 1 else 0,if a then 1 else 0),by cases a <;> cases b <;> norm_num⟩
  refine ⟨G x,?_,?_⟩
  · cases a
    · exact (hW x).mpr rfl
    · exact (hZ x).mpr rfl
  · cases b
    · exact (hL x).mpr rfl
    · exact (hR x).mpr rfl

end PoincareConjecture.M76.PrismBelt
