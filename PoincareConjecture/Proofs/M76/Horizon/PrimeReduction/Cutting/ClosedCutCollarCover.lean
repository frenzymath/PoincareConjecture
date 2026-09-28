import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphRealization
import Mathlib.Topology.LocallyFinite









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]

def collarMiddle {C : Set X} (W : (A × unitInterval) ≃ₜ C) : Set X :=
  (fun z => (W z : X)) '' {z | (1 / 4 : ℝ) ≤ z.2 ∧ (z.2 : ℝ) ≤ 3 / 4}

theorem collarMiddle_subset {C : Set X} (W : (A × unitInterval) ≃ₜ C) :
    collarMiddle W ⊆ C := by
  rintro x ⟨z, _, rfl⟩
  exact (W z).property

theorem mem_collarMiddle_iff {C : Set X} (W : (A × unitInterval) ≃ₜ C)
    (z : A × unitInterval) :
    (W z : X) ∈ collarMiddle W ↔ (1 / 4 : ℝ) ≤ z.2 ∧ (z.2 : ℝ) ≤ 3 / 4 := by
  constructor
  · rintro ⟨w, hw, he⟩
    have h : w = z := W.injective (Subtype.ext he)
    exact h ▸ hw
  · exact fun hz => ⟨z, hz, rfl⟩

theorem isCompact_collarMiddle [CompactSpace A] {C : Set X}
    (W : (A × unitInterval) ≃ₜ C) : IsCompact (collarMiddle W) := by
  have hc : IsClosed {z : A × unitInterval |
      (1 / 4 : ℝ) ≤ z.2 ∧ (z.2 : ℝ) ≤ 3 / 4} :=
    isClosed_Icc.preimage (continuous_subtype_val.comp continuous_snd)
  exact hc.isCompact.image (continuous_subtype_val.comp W.continuous)

theorem collarMiddle_subset_open {C O : Set X} (W : (A × unitInterval) ≃ₜ C)
    (hO : ∀ z, (W z : X) ∈ O ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    collarMiddle W ⊆ O := by
  rintro x ⟨z, hz, rfl⟩
  exact (hO z).mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩

variable {κ : Type*} [Finite κ] {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
  {C : κ → Set X}

def collarCoverOuter (R : Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ C i) : Set R :=
  (Subtype.val : R → X) ⁻¹' (⋃ i, collarMiddle (W i))ᶜ

def collarCoverInner (R : Set X) (O : κ → Set X) : Set R :=
  (Subtype.val : R → X) ⁻¹' ⋃ i, O i

theorem collar_open_cover [T2Space X] [∀ i, CompactSpace (A i)]
    (R : Set X) (O : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ C i)
    (ho : ∀ i, IsOpen (O i))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    IsOpen (collarCoverOuter R W) ∧ IsOpen (collarCoverInner R O) ∧
      collarCoverOuter R W ∪ collarCoverInner R O = univ := by
  have hc : IsClosed (⋃ i, collarMiddle (W i)) :=
    isClosed_iUnion_of_finite fun i => (isCompact_collarMiddle (W i)).isClosed
  refine ⟨hc.isOpen_compl.preimage continuous_subtype_val,
    (isOpen_iUnion ho).preimage continuous_subtype_val, ?_⟩
  apply eq_univ_of_forall
  intro x
  by_cases hx : (x : X) ∈ ⋃ i, collarMiddle (W i)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact Or.inr (mem_iUnion.mpr ⟨i, collarMiddle_subset_open (W i) (hO i) hi⟩)
  · exact Or.inl hx

omit [Finite κ] in
theorem cut_subset_collarCoverOuter
    (R : Set X) (O : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ C i)
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (x : R) (hx : (x : X) ∉ ⋃ i, O i) : x ∈ collarCoverOuter R W := by
  intro hm
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  exact hx (mem_iUnion.mpr ⟨i, collarMiddle_subset_open (W i) (hO i) hi⟩)

omit [Finite κ] in
theorem collarCoverOuter_coordinates
    (R : Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ C i)
    (hCR : ∀ i, C i ⊆ R) (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (i : κ) (z : A i × unitInterval) :
    (⟨W i z, hCR i (W i z).property⟩ : R) ∈ collarCoverOuter R W ↔
      (z.2 : ℝ) < 1 / 4 ∨ (3 / 4 : ℝ) < z.2 := by
  have hm : (W i z : X) ∈ ⋃ j, collarMiddle (W j) ↔
      (W i z : X) ∈ collarMiddle (W i) := by
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact hij ▸ hj
      · exact False.elim (disjoint_left.mp (hdis hij) (W i z).property
          (collarMiddle_subset (W j) hj))
    · exact fun hx => mem_iUnion.mpr ⟨i, hx⟩
  change (¬ (W i z : X) ∈ ⋃ j, collarMiddle (W j)) ↔ _
  rw [hm, mem_collarMiddle_iff]
  simp only [not_and_or, not_le]

end PoincareConjecture.M76
