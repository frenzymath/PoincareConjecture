import PoincareConjecture.Proofs.M76.Wall.BicollarComponentSelection










set_option autoImplicit false

open Set

namespace BrownCollar

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]
  {F C K : Set X}




theorem exists_finite_bicollar_frontier_selection
    (H : (F × Ioo (-1 : ℝ) 1) ≃ₜ C) (hC : IsOpen C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (hside : ∀ z, (H z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ))
    (S : ι → Set X) (hfamily : F = ⋃ i, S i)
    (hS : ∀ i, IsConnected (S i))
    (hopen : ∀ i, IsOpen ((Subtype.val : F → X) ⁻¹' S i))
    {x : X} (hx : x ∈ Kᶜ)
    (hfront : frontier (connectedComponentIn Kᶜ x) ⊆ F)
    (hne : (frontier (connectedComponentIn Kᶜ x)).Nonempty) :
    ∃ J : Finset ι, J.Nonempty ∧
      frontier (connectedComponentIn Kᶜ x) = ⋃ i ∈ J, S i ∧
      ∀ i ∈ J, ∃ U : Set X, IsOpen U ∧ S i ⊆ U ∧ U ⊆ C ∧
        ∀ y ∈ U, y ∈ (connectedComponentIn Kᶜ x)ᶜ ↔ y ∈ K := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hpieces (i : ι) :
      ∃ U : Set X, IsOpen U ∧ S i ⊆ U ∧ U ⊆ C ∧
        ∃ q ∈ Kᶜ, S i ⊆ frontier (connectedComponentIn Kᶜ q) ∧
          ∀ z ∈ Kᶜ,
            ((frontier (connectedComponentIn Kᶜ z) ∩ S i).Nonempty ↔
              connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ q) ∧
            (connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ q →
              ∀ y ∈ U, y ∈ (connectedComponentIn Kᶜ z)ᶜ ↔ y ∈ K) := by
    have hSiF : S i ⊆ F := by
      rw [hfamily]
      exact subset_iUnion S i
    obtain ⟨U, hU, hSU, hUC, G, _, hGb, hGs⟩ :=
      exists_bicollar_restriction H hC hbase hside hSiF (hopen i)
    have hSK : S i ⊆ K := by
      intro y hy
      have hm := (hGs (bicollarBase (⟨y, hy⟩ : S i))).mpr le_rfl
      simpa only [hGb] using hm
    obtain ⟨q, hq, hfrontq, hselect⟩ :=
      exists_bicollar_exterior_component G hU hGb hGs (hS i) hSK
    exact ⟨U, hU, hSU, hUC, q, hq, hfrontq, hselect⟩
  choose U hU hSU hUC q hq hSq hselect using hpieces
  let J : Finset ι := Finset.univ.filter fun i =>
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ (q i)
  have hJ (i : ι) : i ∈ J ↔
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ (q i) := by
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfrontEq : frontier (connectedComponentIn Kᶜ x) = ⋃ i ∈ J, S i := by
    apply Subset.antisymm
    · intro y hy
      have hyF := hfront hy
      rw [hfamily] at hyF
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyF
      have hi : i ∈ J := (hJ i).mpr ((hselect i x hx).1.mp ⟨y, hy, hyi⟩)
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hyi⟩⟩
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      rw [(hJ i).mp hi]
      exact hSq i hyi
  refine ⟨J, ?_, hfrontEq, ?_⟩
  · obtain ⟨y, hy⟩ := hne
    rw [hfrontEq] at hy
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp hy
    exact ⟨i, hi⟩
  · intro i hi
    exact ⟨U i, hU i, hSU i, hUC i, (hselect i x hx).2 ((hJ i).mp hi)⟩

end BrownCollar
