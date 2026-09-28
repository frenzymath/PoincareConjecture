import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Data.Set.Card










set_option autoImplicit false

open Set Topology

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]




structure TwoBranchWindow (r : X → Y) where
  left : OpenPartialHomeomorph X Y
  right : OpenPartialHomeomorph X Y
  target : Set Y
  open_target : IsOpen target
  left_target : left.target = target
  right_target : right.target = target
  left_eq : (left : X → Y) = r
  right_eq : (right : X → Y) = r
  disjoint : Disjoint left.source right.source
  whole_preimage : r ⁻¹' target = left.source ∪ right.source

end Topology





theorem IsLocalHomeomorph.exists_twoBranchWindow
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {r : X → Y} (hr : IsLocalHomeomorph r)
    (hf : ∀ y, (r ⁻¹' {y}).Finite) (hn : ∀ y, (r ⁻¹' {y}).ncard ≤ 2)
    {a b : X} (hab : r a = r b) (hne : a ≠ b) :
    ∃ w : TwoBranchWindow r, a ∈ w.left.source ∧ b ∈ w.right.source := by
  obtain ⟨A, haA, hA⟩ := hr a
  obtain ⟨B, hbB, hB⟩ := hr b
  obtain ⟨V, W, hV, hW, haV, hbW, hVW⟩ := t2_separation hne
  let c₁ := A.restrOpen V hV
  let c₂ := B.restrOpen W hW
  have hc₁ : (c₁ : X → Y) = r := hA.symm
  have hc₂ : (c₂ : X → Y) = r := hB.symm
  have ha : a ∈ c₁.source := ⟨haA, haV⟩
  have hb : b ∈ c₂.source := ⟨hbB, hbW⟩
  have hy₁ : r a ∈ c₁.target := by simpa only [hc₁] using c₁.map_source ha
  have hy₂ : r a ∈ c₂.target := by
    rw [hab]
    simpa only [hc₂] using c₂.map_source hb
  let U := c₁.target ∩ c₂.target
  have hU : IsOpen U := c₁.open_target.inter c₂.open_target
  let e₁ := (c₁.symm.restrOpen U hU).symm
  let e₂ := (c₂.symm.restrOpen U hU).symm
  have he₁ : (e₁ : X → Y) = r := hc₁
  have he₂ : (e₂ : X → Y) = r := hc₂
  have ht₁ : e₁.target = U := by
    change c₁.target ∩ U = U
    exact inter_eq_right.mpr inter_subset_left
  have ht₂ : e₂.target = U := by
    change c₂.target ∩ U = U
    exact inter_eq_right.mpr inter_subset_right
  have hs₁ : e₁.source = c₁.source ∩ r ⁻¹' U := by
    change c₁.source ∩ c₁ ⁻¹' U = c₁.source ∩ r ⁻¹' U
    rw [hc₁]
  have hs₂ : e₂.source = c₂.source ∩ r ⁻¹' U := by
    change c₂.source ∩ c₂ ⁻¹' U = c₂.source ∩ r ⁻¹' U
    rw [hc₂]
  have hdis : Disjoint e₁.source e₂.source := by
    apply hVW.mono
    · intro x hx
      rw [hs₁] at hx
      exact hx.1.2
    · intro x hx
      rw [hs₂] at hx
      exact hx.1.2
  have hwhole : r ⁻¹' U = e₁.source ∪ e₂.source := by
    apply Subset.antisymm
    · intro x hx
      have hx₁ : r x ∈ e₁.target := by rw [ht₁]; exact hx
      have hx₂ : r x ∈ e₂.target := by rw [ht₂]; exact hx
      let u := e₁.symm (r x)
      let v := e₂.symm (r x)
      have hu : u ∈ e₁.source := e₁.map_target hx₁
      have hv : v ∈ e₂.source := e₂.map_target hx₂
      have huv : u ≠ v := hdis.ne_of_mem hu hv
      have hru : r u = r x := (congrFun he₁ u).symm.trans (e₁.right_inv hx₁)
      have hrv : r v = r x := (congrFun he₂ v).symm.trans (e₂.right_inv hx₂)
      have hpair : ({u, v} : Set X) ⊆ r ⁻¹' {r x} := by
        intro z hz
        simp only [mem_insert_iff, mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hru
        · exact hrv
      have heq : ({u, v} : Set X) = r ⁻¹' {r x} :=
        eq_of_subset_of_ncard_le hpair (by rw [ncard_pair huv]; exact hn (r x)) (hf (r x))
      have hxuv : x ∈ ({u, v} : Set X) := heq.superset rfl
      simp only [mem_insert_iff, mem_singleton_iff] at hxuv
      rcases hxuv with hxu | hxv
      · rw [hxu]
        exact Or.inl hu
      · rw [hxv]
        exact Or.inr hv
    · intro x hx
      rcases hx with hx | hx
      · rw [hs₁] at hx
        exact hx.2
      · rw [hs₂] at hx
        exact hx.2
  refine ⟨⟨e₁, e₂, U, hU, ht₁, ht₂, he₁, he₂, hdis, hwhole⟩, ?_, ?_⟩
  · rw [hs₁]
    exact ⟨ha, hy₁, hy₂⟩
  · rw [hs₂]
    refine ⟨hb, ?_⟩
    change r b ∈ U
    rw [← hab]
    exact ⟨hy₁, hy₂⟩
