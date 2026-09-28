import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.RectangleCapSupport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleBoundaryCover



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem original_rectangle_cut_support_constant
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [DecidableEq ι]
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite) {g : E → X} {S : Set X} {t : Finset E}
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B : Set E} (cut : ι → Set E) (owner : ∀ f, (D f).Arc → ι)
    (howner : ∀ f j, (D f).arc j ⊆ cut (owner f j))
    (hcutContact : ∀ f k i, (D f).carrier k ∩ cut i =
      (if owner f ((D f).cap k false) = i then (D f).arc ((D f).cap k false) else ∅) ∪
      (if owner f ((D f).cap k true) = i then (D f).arc ((D f).cap k true) else ∅))
    (hconn : IsPreconnected (⋃ z : CutBallRectangle D B, (D z.1.1).carrier z.1.2))
    (hcontact : ∀ z w : CutBallRectangle D B, z ≠ w →
      ((D z.1.1).carrier z.1.2 ∩ (D w.1.1).carrier w.1.2).Nonempty →
      ∃ b c, (D z.1.1).side z.1.2 b = (D w.1.1).side w.1.2 c) :
    ∀ z w : CutBallRectangle D B, ∀ i,
      ((D z.1.1).carrier z.1.2 ∩ cut i).Nonempty ↔
        ((D w.1.1).carrier w.1.2 ∩ cut i).Nonempty := by
  classical
  let := K.finite_faceOfCard hK 3
  let M (z : CutBallRectangle D B) := (D z.1.1).carrier z.1.2
  let label (z : CutBallRectangle D B) : Set ι := {i | (M z ∩ cut i).Nonempty}
  have heq := eq_labels_of_connected_finite_closed_cover M
    (fun z => ((D z.1.1).regionBall z.1.2).isCompact.isClosed)
    (fun z => ((D z.1.1).region_core_nonempty z.1.2).mono sdiff_subset) hconn label
    (by
      intro z w hmeet
      by_cases hzw : z = w
      · exact congrArg label hzw
      obtain ⟨b,c,hside⟩ := hcontact z w hzw hmeet
      ext i
      change (M z ∩ cut i).Nonempty ↔ (M w ∩ cut i).Nonempty
      rw [(D z.1.1).carrier_meets_cut_iff cut (owner z.1.1) (howner z.1.1)
          (hcutContact z.1.1),
        ←(D z.1.1).side_meets_cut_iff cut (owner z.1.1) (howner z.1.1)
          (hcutContact z.1.1) z.1.2 b,hside,
        (D w.1.1).side_meets_cut_iff cut (owner w.1.1) (howner w.1.1)
          (hcutContact w.1.1) w.1.2 c,
        (D w.1.1).carrier_meets_cut_iff cut (owner w.1.1) (howner w.1.1)
          (hcutContact w.1.1)])
  intro z w i
  exact Set.ext_iff.mp (heq z w) i

end PoincareConjecture.M76.PrismBelt
