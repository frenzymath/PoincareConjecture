import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Image
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false

open Set

namespace Set

variable {X Y ι : Type*}

noncomputable def alexanderCurveCount [Finite ι] (D : ι → Set X) : ℕ := by
  classical
  exact if Pairwise (fun i j => Disjoint (D i) (D j)) then 0 else Nat.card ι

variable [Finite ι]

theorem alexanderCurveCount_le_card (D : ι → Set X) :
    alexanderCurveCount D ≤ Nat.card ι := by
  classical
  unfold alexanderCurveCount
  split_ifs <;> omega

theorem alexanderCurveCount_eq_zero_iff (D : ι → Set X) :
    alexanderCurveCount D = 0 ↔ Pairwise (fun i j => Disjoint (D i) (D j)) := by
  classical
  constructor
  · intro hz i j hij
    by_contra hdisj
    have hbranch : ¬ Pairwise (fun i j => Disjoint (D i) (D j)) :=
      fun h => hdisj (h hij)
    have hcount : alexanderCurveCount D = Nat.card ι := by
      simp only [alexanderCurveCount, if_neg hbranch]
    have hpos : 0 < Nat.card ι := Nat.card_pos_iff.mpr ⟨⟨i⟩, inferInstance⟩
    omega
  · intro h
    simp only [alexanderCurveCount, if_pos h]

theorem alexanderCurveCount_image (D : ι → Set X) {s : Set X}
    (hD : ∀ i, D i ⊆ s) (f : X → Y) (hf : InjOn f s) :
    alexanderCurveCount (fun i => f '' D i) = alexanderCurveCount D := by
  classical
  have hdisj : Pairwise (fun i j => Disjoint (f '' D i) (f '' D j)) ↔
      Pairwise (fun i j => Disjoint (D i) (D j)) := by
    constructor
    · intro h i j hij
      refine disjoint_left.mpr ?_
      intro x hxi hxj
      exact disjoint_left.mp (h hij) ⟨x, hxi, rfl⟩ ⟨x, hxj, rfl⟩
    · intro h i j hij
      refine disjoint_left.mpr ?_
      intro y hyi hyj
      obtain ⟨x, hxi, hxy⟩ := hyi
      obtain ⟨z, hzj, hzy⟩ := hyj
      have hxz : x = z := hf (hD i hxi) (hD j hzj) (hxy.trans hzy.symm)
      exact disjoint_left.mp (h hij) hxi (hxz.symm ▸ hzj)
  simp only [alexanderCurveCount, hdisj]

theorem alexanderCurveCount_partition_le (D : ι → Set X) (I : Set ι) :
    alexanderCurveCount (fun i : I => D i) +
      alexanderCurveCount (fun i : (Iᶜ : Set ι) => D i) ≤ alexanderCurveCount D := by
  classical
  by_cases h : Pairwise (fun i j => Disjoint (D i) (D j))
  · have h₀ : Pairwise (fun i j : I => Disjoint (D i) (D j)) := by
      intro i j hij
      exact h (fun heq => hij (Subtype.ext heq))
    have h₁ : Pairwise (fun i j : (Iᶜ : Set ι) => Disjoint (D i) (D j)) := by
      intro i j hij
      exact h (fun heq => hij (Subtype.ext heq))
    simp only [alexanderCurveCount, if_pos h, if_pos h₀, if_pos h₁, add_zero, le_refl]
  · have h₀ := alexanderCurveCount_le_card (fun i : I => D i)
    have h₁ := alexanderCurveCount_le_card (fun i : (Iᶜ : Set ι) => D i)
    have hcard : Nat.card I + Nat.card (Iᶜ : Set ι) = Nat.card ι := by
      rw [← Nat.card_sum]
      exact Nat.card_congr (Equiv.Set.sumCompl I)
    have hcount : alexanderCurveCount D = Nat.card ι := by
      simp only [alexanderCurveCount, if_neg h]
    rw [hcount]
    omega

theorem alexanderCurveCount_partition_after_deletion
    (D : ι → Set X) (hbranch : ¬ Pairwise (fun i j => Disjoint (D i) (D j)))
    (p : ι) (I : Set {i : ι // i ≠ p}) :
    alexanderCurveCount (fun i : I => D i.val.val) +
        alexanderCurveCount (fun i : (Iᶜ : Set {i : ι // i ≠ p}) => D i.val.val) + 1 ≤
        alexanderCurveCount D ∧
      alexanderCurveCount (fun i : I => D i.val.val) < alexanderCurveCount D ∧
      alexanderCurveCount (fun i : (Iᶜ : Set {i : ι // i ≠ p}) => D i.val.val) <
        alexanderCurveCount D := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hpartition : Nat.card I + Nat.card (Iᶜ : Set {i : ι // i ≠ p}) =
      Nat.card {i : ι // i ≠ p} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.Set.sumCompl I)
  have hdelete : Nat.card {i : ι // i ≠ p} = Nat.card ι - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simpa only [Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun i : ι => i = p))
  have hpos : 0 < Nat.card ι := Nat.card_pos_iff.mpr ⟨⟨p⟩, inferInstance⟩
  have h₀ := alexanderCurveCount_le_card (fun i : I => D i.val.val)
  have h₁ := alexanderCurveCount_le_card
    (fun i : (Iᶜ : Set {i : ι // i ≠ p}) => D i.val.val)
  have hcount : alexanderCurveCount D = Nat.card ι := by
    simp only [alexanderCurveCount, if_neg hbranch]
  rw [hcount]
  exact ⟨by omega, by omega, by omega⟩

end Set

namespace Homeomorph

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]

theorem alexanderCurveCount_image {s : Set X} {t : Set Y} (e : s ≃ₜ t)
    (D : ι → Set X) (hD : ∀ i, D i ⊆ s) (f : X → Y)
    (hrep : ∀ x : s, (e x : Y) = f x) :
    Set.alexanderCurveCount (fun i => f '' D i) = Set.alexanderCurveCount D := by
  apply Set.alexanderCurveCount_image D hD f
  intro x hx y hy hxy
  have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa only [hrep] using hxy
  exact congrArg Subtype.val (e.injective hexy)

end Homeomorph
