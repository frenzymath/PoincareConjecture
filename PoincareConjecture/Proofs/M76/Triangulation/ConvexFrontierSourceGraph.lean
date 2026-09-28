import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierMarkedDecomposition
import PoincareConjecture.Proofs.M76.Mathlib.MarkedFourRegionSigns

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_convex_frontier_source_graph
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hspace : K.space = C) (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hq : q ∈ interior C) (hqA : A q = 0)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPC : P.boundary ℝ ⊆ frontier C)
    {a b : E} (hab : a ≠ b)
    (hzero : P.boundary ℝ ∩ {x | A x = 0} = {a, b})
    (hneg : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hpos : ∃ x ∈ P.boundary ℝ, 0 < A x) :
    ∃ arc disk : Bool × Bool → Set E,
      (∀ i, IsFinitePLBallPair ℝ (arc i) {a, b}) ∧
      Pairwise (fun i j => arc i ∩ arc j = {a, b}) ∧
      (∀ i, IsFinitePLBallPair (ℝ × ℝ) (disk i)
        (arc (false, i.2) ∪ arc (true, i.1))) ∧
      (∀ i, disk i ∩ (⋃ j, arc j) = arc (false, i.2) ∪ arc (true, i.1)) ∧
      Pairwise (fun i j => disk i ∩ disk j ⊆ ⋃ j, arc j) ∧
      (⋃ i, disk i) = frontier C ∧
      (⋃ i, arc i) = frontier C ∩ (P.boundary ℝ ∪ {x | A x = 0}) ∧
      arc (false, false) ∪ arc (false, true) = frontier C ∩ {x | A x = 0} ∧
      (∀ i : Bool, arc (true, i) =
        P.boundary ℝ ∩ {x | if i then A x ≤ 0 else 0 ≤ A x}) ∧
      ∀ i : Bool, disk (i, false) ∪ disk (i, true) =
        frontier C ∩ {x | if i then A x ≤ 0 else 0 ≤ A x} := by
  obtain ⟨arc, disk, hArc, hArcInter, hDisk, hDiskInter,
    hwhole, hequator, hlink, hposUnion, hnegUnion⟩ :=
    K.exists_convex_frontier_marked_decomposition hK hC hcv hspace hdim A hq hqA
      P hP hinj hPC hab hzero hneg hpos
  obtain ⟨hcontact, hpair, _⟩ :=
    four_disk_graph_contacts arc disk (fun i => (hDisk i).1) hDiskInter
  have hsigned := four_disk_signed_link_arcs arc disk A
    (fun i => (hDisk i).1) hlink
    (fun x hx => (hposUnion.subset hx).2) (fun x hx => (hnegUnion.subset hx).2)
    hzero.subset (fun i => (hArc (true, i)).1)
  have hgraph : (⋃ i, arc i) = frontier C ∩ (P.boundary ℝ ∪ {x | A x = 0}) := by
    have hsplit : (⋃ i, arc i) =
        (arc (false, false) ∪ arc (false, true)) ∪
          (arc (true, false) ∪ arc (true, true)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨⟨i, j⟩, hx⟩ := mem_iUnion.mp hx
        cases i <;> cases j
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr hx)
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
      · rintro ((hx | hx) | (hx | hx))
        · exact mem_iUnion.mpr ⟨(false, false), hx⟩
        · exact mem_iUnion.mpr ⟨(false, true), hx⟩
        · exact mem_iUnion.mpr ⟨(true, false), hx⟩
        · exact mem_iUnion.mpr ⟨(true, true), hx⟩
    rw [hsplit, hequator, hlink]
    ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, Or.inr hx.2⟩
      · exact ⟨hPC hx, Or.inl hx⟩
    · rintro ⟨hxC, hxP | hxA⟩
      · exact Or.inr hxP
      · exact Or.inl ⟨hxC, hxA⟩
  refine ⟨arc, disk, hArc, hArcInter, hDisk, hcontact, hpair, hwhole,
    hgraph, hequator, ?_, ?_⟩
  · intro i
    cases i
    · exact hsigned.1
    · exact hsigned.2
  · intro i
    cases i
    · exact hposUnion
    · exact hnegUnion

end Geometry.SimplicialComplex
