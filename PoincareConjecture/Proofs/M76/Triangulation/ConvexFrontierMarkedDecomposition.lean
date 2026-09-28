import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierFourRegions
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFourDiskGluing










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_convex_frontier_marked_decomposition (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
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
      Pairwise (fun i j => disk i ∩ disk j ⊆ arc (false, i.2) ∪ arc (true, i.1)) ∧
      (⋃ i, disk i) = frontier C ∧
      arc (false, false) ∪ arc (false, true) = frontier C ∩ {x | A x = 0} ∧
      arc (true, false) ∪ arc (true, true) = P.boundary ℝ ∧
      disk (false, false) ∪ disk (false, true) = frontier C ∩ {x | 0 ≤ A x} ∧
      disk (true, false) ∪ disk (true, true) = frontier C ∩ {x | A x ≤ 0} := by
  obtain ⟨U, V, d₀₀, d₀₁, d₁₀, d₁₁, hU, hV, hUV, hUVi,
      h₀₀, h₀₁, h₁₀, h₁₁, hposUnion, hnegUnion, hposInter, hnegInter,
      _, _, _, _, hUinter, hVinter, hdiag₀, hdiag₁, hwhole⟩ :=
    K.exists_convex_frontier_four_regions hK hC hcv hspace hdim A hq hqA
      P hP hinj hPC hab hzero hneg hpos
  let Wpos := P.boundary ℝ ∩ {x | 0 ≤ A x}
  let Wneg := P.boundary ℝ ∩ {x | A x ≤ 0}
  obtain ⟨hWneg, hWpos⟩ := P.isFinitePLBallPair_signed_halves hP hinj A
    A.continuous_of_finiteDimensional.continuousOn hab hzero hneg hpos
  have hsignInter : Wpos ∩ Wneg = {a, b} := by
    apply Subset.antisymm
    · intro x hx
      exact hzero.subset ⟨hx.1.1, le_antisymm hx.2.2 hx.1.2⟩
    · exact fun x hx => ⟨hWpos.1 hx, hWneg.1 hx⟩
  have hcross {T W : Set E}
      (hT : IsFinitePLBallPair ℝ T {a, b}) (hW : IsFinitePLBallPair ℝ W {a, b})
      (hTR : T ⊆ frontier C ∩ {x | A x = 0}) (hWP : W ⊆ P.boundary ℝ) :
      T ∩ W = {a, b} := by
    apply Subset.antisymm
    · exact fun x hx => hzero.subset ⟨hWP hx.2, (hTR hx.1).2⟩
    · exact fun x hx => ⟨hT.1 hx, hW.1 hx⟩
  have hUpos : U ∩ Wpos = {a, b} :=
    hcross hU hWpos (subset_union_left.trans hUV.subset) inter_subset_left
  have hUneg : U ∩ Wneg = {a, b} :=
    hcross hU hWneg (subset_union_left.trans hUV.subset) inter_subset_left
  have hVpos : V ∩ Wpos = {a, b} :=
    hcross hV hWpos (subset_union_right.trans hUV.subset) inter_subset_left
  have hVneg : V ∩ Wneg = {a, b} :=
    hcross hV hWneg (subset_union_right.trans hUV.subset) inter_subset_left
  let arc : Bool × Bool → Set E := fun i => match i with
    | (false, false) => U
    | (false, true) => V
    | (true, false) => Wpos
    | (true, true) => Wneg
  let disk : Bool × Bool → Set E := fun i => match i with
    | (false, false) => d₀₀
    | (false, true) => d₀₁
    | (true, false) => d₁₀
    | (true, true) => d₁₁
  have hArc (i : Bool × Bool) : IsFinitePLBallPair ℝ (arc i) {a, b} := by
    rcases i with ⟨i, j⟩
    cases i <;> cases j
    · exact hU
    · exact hV
    · exact hWpos
    · exact hWneg
  have hArcInter : Pairwise (fun i j => arc i ∩ arc j = {a, b}) := by
    intro i j hij
    rcases i with ⟨i₀, i₁⟩
    rcases j with ⟨j₀, j₁⟩
    cases i₀ <;> cases i₁ <;> cases j₀ <;> cases j₁
    all_goals first
      | exact (hij rfl).elim
      | exact hUVi
      | exact (inter_comm V U).trans hUVi
      | exact hUpos
      | exact (inter_comm Wpos U).trans hUpos
      | exact hUneg
      | exact (inter_comm Wneg U).trans hUneg
      | exact hVpos
      | exact (inter_comm Wpos V).trans hVpos
      | exact hVneg
      | exact (inter_comm Wneg V).trans hVneg
      | exact hsignInter
      | exact (inter_comm Wneg Wpos).trans hsignInter
  have hDisk (i : Bool × Bool) : IsFinitePLBallPair (ℝ × ℝ) (disk i)
      (arc (false, i.2) ∪ arc (true, i.1)) := by
    rcases i with ⟨i, j⟩
    cases i <;> cases j
    · exact h₀₀
    · simpa only [arc, disk, union_comm] using h₀₁
    · exact h₁₀
    · simpa only [arc, disk, union_comm] using h₁₁
  have hDiskInter : Pairwise (fun i j =>
      disk i ∩ disk j ⊆ arc (false, i.2) ∪ arc (true, i.1)) := by
    intro i j hij
    have hmarks : ({a, b} : Set E) ⊆ arc (false, i.2) ∪ arc (true, i.1) :=
      (hArc (false, i.2)).1.trans subset_union_left
    rcases i with ⟨i₀, i₁⟩
    rcases j with ⟨j₀, j₁⟩
    cases i₀ <;> cases i₁ <;> cases j₀ <;> cases j₁
    all_goals first
      | exact (hij rfl).elim
      | exact hposInter.subset.trans subset_union_right
      | exact ((inter_comm d₀₁ d₀₀).trans hposInter).subset.trans subset_union_right
      | exact hnegInter.subset.trans subset_union_right
      | exact ((inter_comm d₁₁ d₁₀).trans hnegInter).subset.trans subset_union_right
      | exact hUinter.subset.trans subset_union_left
      | exact ((inter_comm d₁₀ d₀₀).trans hUinter).subset.trans subset_union_left
      | exact hVinter.subset.trans subset_union_left
      | exact ((inter_comm d₁₁ d₀₁).trans hVinter).subset.trans subset_union_left
      | exact hdiag₀.subset.trans hmarks
      | exact ((inter_comm d₁₁ d₀₀).trans hdiag₀).subset.trans hmarks
      | exact hdiag₁.subset.trans hmarks
      | exact ((inter_comm d₁₀ d₀₁).trans hdiag₁).subset.trans hmarks
  have hDiskUnion : (⋃ i, disk i) = frontier C := by
    rw [← hwhole]
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
  have hLinkUnion : Wpos ∪ Wneg = P.boundary ℝ := by
    ext x
    constructor
    · exact fun hx => hx.elim And.left And.left
    · intro hx
      rcases le_total 0 (A x) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  exact ⟨arc, disk, hArc, hArcInter, hDisk, hDiskInter,
    hDiskUnion, hUV, hLinkUnion, hposUnion, hnegUnion⟩

end Geometry.SimplicialComplex
