import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.CircleSurgeryGraph










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)


def selectedCircleSurgeryFamily {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool) : κ → Set X :=
  Function.update S i (new b)


def selectedCircleSurgeryIndex {κ : Type*} [DecidableEq κ] (i : κ) (b : Bool)
    (j : κ) : {j : κ // j ≠ i} ⊕ Bool :=
  if h : j = i then Sum.inr b else Sum.inl ⟨j, h⟩

theorem selectedCircleSurgeryIndex_injective {κ : Type*} [DecidableEq κ]
    (i : κ) (b : Bool) : Function.Injective (selectedCircleSurgeryIndex i b) := by
  intro j k hjk
  by_cases hj : j = i <;> by_cases hk : k = i
  · exact hj.trans hk.symm
  · simp only [selectedCircleSurgeryIndex, dif_pos hj, dif_neg hk] at hjk
    cases hjk
  · simp only [selectedCircleSurgeryIndex, dif_neg hj, dif_pos hk] at hjk
    cases hjk
  · simp only [selectedCircleSurgeryIndex, dif_neg hj, dif_neg hk] at hjk
    exact congrArg Subtype.val (Sum.inl.inj hjk)

theorem selectedCircleSurgeryFamily_eq_index {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool) (j : κ) :
    selectedCircleSurgeryFamily S i new b j =
      circleSurgeryFamily S i new (selectedCircleSurgeryIndex i b j) := by
  by_cases hj : j = i
  · subst j
    simp [selectedCircleSurgeryFamily, selectedCircleSurgeryIndex, circleSurgeryFamily]
  · simp [selectedCircleSurgeryFamily, selectedCircleSurgeryIndex, circleSurgeryFamily, hj]

theorem selectedCircleSurgeryFamily_iUnion {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool) :
    (⋃ j, selectedCircleSurgeryFamily S i new b j) =
      (⋃ j : {j : κ // j ≠ i}, S j.val) ∪ new b := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · subst j
      exact Or.inr (by simpa [selectedCircleSurgeryFamily] using hj)
    · exact Or.inl (mem_iUnion.mpr ⟨⟨j, hji⟩,
        by simpa [selectedCircleSurgeryFamily, hji] using hj⟩)
  · rintro (hx | hx)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨j.val,
        by simpa [selectedCircleSurgeryFamily, j.property] using hj⟩
    · exact mem_iUnion.mpr ⟨i, by simpa [selectedCircleSurgeryFamily] using hx⟩

theorem selectedCircleSurgeryFamily_subset {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool) :
    (⋃ j, selectedCircleSurgeryFamily S i new b j) ⊆ ⋃ j, circleSurgeryFamily S i new j := by
  intro x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨selectedCircleSurgeryIndex i b j,
    (selectedCircleSurgeryFamily_eq_index S i new b j).subset hj⟩

theorem selectedCircleSurgeryFamily_union_omitted {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool) :
    (⋃ j, selectedCircleSurgeryFamily S i new b j) ∪ new (!b) =
      ⋃ j, circleSurgeryFamily S i new j := by
  rw [selectedCircleSurgeryFamily_iUnion, circleSurgeryFamily_iUnion, union_assoc]
  cases b
  · simp only [Bool.not_false]
    rw [union_comm (new false) (new true)]
  · rfl

theorem selectedCircleSurgeryFamily_disjoint_omitted {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool)
    (hfull : Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k)) :
    Disjoint (⋃ j, selectedCircleSurgeryFamily S i new b j) (new (!b)) := by
  apply disjoint_left.mpr
  intro x hx hxnew
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  have hne : selectedCircleSurgeryIndex i b j ≠ Sum.inr (!b) := by
    by_cases hji : j = i
    · simpa only [selectedCircleSurgeryIndex, dif_pos hji, ne_eq, Sum.inr.injEq] using
        Bool.self_ne_not b
    · simp only [selectedCircleSurgeryIndex, dif_neg hji, ne_eq, Sum.inl_ne_inr, not_false_eq_true]
  exact disjoint_left.mp (hfull hne)
    ((selectedCircleSurgeryFamily_eq_index S i new b j).subset hj) hxnew



theorem selectedCircleSurgeryFamily_geometry
    {X ι κ : Type*} [TopologicalSpace X] [DecidableEq κ] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {Z : Set X}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool)
    (sfull : ∀ j, ChartwisePLSphere e (circleSurgeryFamily S i new j))
    (hfull : Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k))
    (hmarked : Disjoint (⋃ j, circleSurgeryFamily S i new j) Z) :
    Nonempty (∀ j, ChartwisePLSphere e (selectedCircleSurgeryFamily S i new b j)) ∧
    (Pairwise fun j k => Disjoint (selectedCircleSurgeryFamily S i new b j)
      (selectedCircleSurgeryFamily S i new b k)) ∧
    Disjoint (⋃ j, selectedCircleSurgeryFamily S i new b j) Z ∧
    (⋃ j, selectedCircleSurgeryFamily S i new b j) ⊆ ⋃ j, circleSurgeryFamily S i new j ∧
    Nat.card (Set.range (selectedCircleSurgeryFamily S i new b)) = Nat.card κ := by
  have hs : ∀ j, ChartwisePLSphere e (selectedCircleSurgeryFamily S i new b j) := by
    intro j
    rw [selectedCircleSurgeryFamily_eq_index]
    exact sfull _
  have hd : Pairwise fun j k => Disjoint (selectedCircleSurgeryFamily S i new b j)
      (selectedCircleSurgeryFamily S i new b k) := by
    intro j k hjk
    rw [selectedCircleSurgeryFamily_eq_index, selectedCircleSurgeryFamily_eq_index]
    exact hfull (fun h => hjk (selectedCircleSurgeryIndex_injective i b h))
  have hinj : Function.Injective (selectedCircleSurgeryFamily S i new b) := by
    intro j k hjk
    by_contra hne
    obtain ⟨x, hx⟩ := (show (Metric.sphere (0 : V3) 1).Nonempty from
      NormedSpace.sphere_nonempty.mpr zero_le_one)
    let y := (hs j).parametrization ⟨x, hx⟩
    exact disjoint_left.mp (hd hne) y.property (hjk ▸ y.property)
  exact ⟨⟨hs⟩, hd,
    hmarked.mono_left (selectedCircleSurgeryFamily_subset S i new b),
    selectedCircleSurgeryFamily_subset S i new b, Nat.card_range_of_injective hinj⟩

end PoincareConjecture.M76
