import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutBoundaryArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutInteriorEmbedding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.FourArcRectangle









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)
  (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

include hbound A

theorem exists_marked_cut_rectangle :
    ∃ C : (PeriodicSquare.squareCarrier 1) ≃ₜ A.carrier, C.IsFinitePL ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 0 ↔ x.val.2 = 0) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 2 ↔ x.val.2 = 1) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 3 ↔ x.val.1 = 0) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 1 ↔ x.val.1 = 1) := by
  have hcover : (A.longBoundaryArc 0 ∪ A.longBoundaryArc 2) ∪
      (A.longBoundaryArc 3 ∪ A.longBoundaryArc 1) = A.rim := by
    rw [← A.longBoundaryArcs_cover]
    ext p
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro ((h | h) | (h | h))
      · exact ⟨0, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> tauto
  have hM : IsFinitePLBallPair (ℝ × ℝ) A.carrier
      ((A.longBoundaryArc 0 ∪ A.longBoundaryArc 2) ∪
        (A.longBoundaryArc 3 ∪ A.longBoundaryArc 1)) := hcover.symm ▸ A.disk
  have hW := A.longBoundaryArc_isFinitePLInterval hbound 0
  have hZ := A.longBoundaryArc_isFinitePLInterval hbound 2
  have hL := A.longBoundaryArc_isFinitePLInterval hbound 3
  have hR := A.longBoundaryArc_isFinitePLInterval hbound 1
  have hWL := A.longBoundaryArc_inter_next hbound 3
  have hWR := A.longBoundaryArc_inter_next hbound 0
  have hZL := A.longBoundaryArc_inter_next hbound 2
  have hZR := A.longBoundaryArc_inter_next hbound 1
  have hWZ := A.longBoundaryArc_disjoint_opposite hbound 0
  have hLR := A.longBoundaryArc_disjoint_opposite hbound 3
  simp only [show (0 : Fin 4) - 1 = 3 from rfl,
    show (2 : Fin 4) - 1 = 1 from rfl, show (3 : Fin 4) - 1 = 2 from rfl,
    show (1 : Fin 4) - 1 = 0 from rfl, show (3 : Fin 4) + 1 = 0 from rfl,
    show (0 : Fin 4) + 1 = 1 from rfl, show (2 : Fin 4) + 1 = 3 from rfl,
    show (1 : Fin 4) + 1 = 2 from rfl, show (0 : Fin 4) + 2 = 2 from rfl,
    show (3 : Fin 4) + 2 = 1 from rfl] at hW hZ hL hR hWL hWR hZL hZR hWZ hLR
  have hp : A.gapCenter 3 ≠ A.gapCenter 0 := A.gapCenters_injective.ne (by decide)
  have hq : A.gapCenter 2 ≠ A.gapCenter 1 := A.gapCenters_injective.ne (by decide)
  have h₀ : A.gapCenter 3 ≠ A.gapCenter 2 := A.gapCenters_injective.ne (by decide)
  have h₁ : A.gapCenter 0 ≠ A.gapCenter 1 := A.gapCenters_injective.ne (by decide)
  exact exists_four_arc_rectangle hM hW
    (by rw [Set.pair_comm]; exact hZ)
    (by rw [Set.pair_comm]; exact hL) hR hp hq h₀ h₁ hWZ hLR
    (by simpa only [inter_comm] using hWL) hWR hZL
    (by simpa only [inter_comm] using hZR)




theorem exists_marked_square_filling :
    ∃ F : (ℝ × ℝ) → E,
      FinitePiecewiseAffineOn F (PeriodicSquare.squareCarrier 1) ∧
      F '' PeriodicSquare.squareCarrier 1 = K.space ∧
      (∀ x ∈ PeriodicSquare.squareCarrier 1, F x = A.sectors.center ↔
        (x.1 = 0 ∨ x.1 = 1) ∧ (x.2 = 0 ∨ x.2 = 1)) ∧
      (∀ x ∈ PeriodicSquare.squareCarrier 1, ∀ y ∈ PeriodicSquare.squareCarrier 1,
        F x = F y → x = y ∨
          (x.1 = 0 ∨ x.1 = 1 ∨ x.2 = 0 ∨ x.2 = 1) ∧
          (y.1 = 0 ∨ y.1 = 1 ∨ y.2 = 0 ∨ y.2 = 1)) := by
  obtain ⟨C, hC, hw, hz, hl, hr⟩ := A.exists_marked_cut_rectangle hbound
  obtain ⟨f, hf, hCf⟩ := hC
  have hmap : MapsTo f (PeriodicSquare.squareCarrier 1) A.carrier := by
    intro x hx
    rw [← hCf ⟨x, hx⟩]
    exact (C ⟨x, hx⟩).property
  have him : f '' PeriodicSquare.squareCarrier 1 = A.carrier := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hmap hx
    · intro p hp
      obtain ⟨x, hx⟩ := C.surjective ⟨p, hp⟩
      exact ⟨x, x.property, (hCf x).symm.trans (congrArg Subtype.val hx)⟩
  have hrim (x : PeriodicSquare.squareCarrier 1) (hx : (C x).val ∈ A.rim) :
      x.val.1 = 0 ∨ x.val.1 = 1 ∨ x.val.2 = 0 ∨ x.val.2 = 1 := by
    rw [← A.longBoundaryArcs_cover] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inr (Or.inr (Or.inl ((hw x).mp hi)))
    · exact Or.inr (Or.inl ((hr x).mp hi))
    · exact Or.inr (Or.inr (Or.inr ((hz x).mp hi)))
    · exact Or.inl ((hl x).mp hi)
  have hc (x : PeriodicSquare.squareCarrier 1) :
      (A.sourceMap) (C x) = A.sectors.center ↔
        (x.val.1 = 0 ∨ x.val.1 = 1) ∧ (x.val.2 = 0 ∨ x.val.2 = 1) := by
    constructor
    · intro hx
      have hm : (C x).val ∈ A.carrier ∩ A.sourceMap ⁻¹' {A.sectors.center} :=
        ⟨(C x).property, hx⟩
      rw [A.sourceMap_center_fiber hbound] at hm
      obtain ⟨j, hj⟩ := hm
      obtain ⟨i, hi⟩ := A.matching.surjective j
      have hp : (C x).val = A.gapCenter i := by
        change (C x).val = A.sectorCopy (A.matching i) A.sectors.center
        rw [hi]
        exact hj.symm
      have hs := (A.longBoundaryArc_inter_next hbound i).symm.subset hp
      fin_cases i
      · exact ⟨Or.inr ((hr x).mp hs.2), Or.inl ((hw x).mp hs.1)⟩
      · exact ⟨Or.inr ((hr x).mp hs.1), Or.inr ((hz x).mp hs.2)⟩
      · exact ⟨Or.inl ((hl x).mp hs.2), Or.inr ((hz x).mp hs.1)⟩
      · exact ⟨Or.inl ((hl x).mp hs.1), Or.inl ((hw x).mp hs.2)⟩
    · have hcorner (i : Fin 4) (hi : (C x).val ∈ A.longBoundaryArc i)
          (hj : (C x).val ∈ A.longBoundaryArc (i + 1)) :
          (A.sourceMap) (C x) = A.sectors.center := by
        have he : (C x).val = A.gapCenter i :=
          (A.longBoundaryArc_inter_next hbound i).subset ⟨hi, hj⟩
        rw [he]
        rfl
      rintro ⟨hx | hx, hy | hy⟩
      · exact hcorner 3 ((hl x).mpr hx) ((hw x).mpr hy)
      · exact hcorner 2 ((hz x).mpr hy) ((hl x).mpr hx)
      · exact hcorner 0 ((hw x).mpr hy) ((hr x).mpr hx)
      · exact hcorner 1 ((hr x).mpr hx) ((hz x).mpr hy)
  refine ⟨A.sourceMap ∘ f, A.sourceMapPL.comp hf hmap, ?_, ?_, ?_⟩
  · rw [image_comp, him]
    exact A.sourceMap_image
  · intro x hx
    have h := hc ⟨x, hx⟩
    rw [hCf] at h
    exact h
  · intro x hx y hy heq
    have he : (A.sourceMap) (C ⟨x, hx⟩) = (A.sourceMap) (C ⟨y, hy⟩) := by
      rw [hCf, hCf]
      exact heq
    rcases A.sourceMap_fiber_eq_or_rim hbound (C ⟨x, hx⟩).property
      (C ⟨y, hy⟩).property he with h | h
    · exact Or.inl (congrArg Subtype.val (C.injective (Subtype.ext h)))
    · exact Or.inr ⟨hrim ⟨x, hx⟩ h.1, hrim ⟨y, hy⟩ h.2⟩

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
