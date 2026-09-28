import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_two_band_label_matching
    (U V : Fin 2 → (E2 × ℝ) → E3) (H : E3 → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hU : ∀ i : Fin 2,
      ContinuousOn (U i) (sphere (0 : E2) 1 ×ˢ Icc a b))
    (hV : ∀ i : Fin 2,
      ContinuousOn (V i) (sphere (0 : E2) 1 ×ˢ Icc a b))
    (hUh : ∀ (i : Fin 2) (x : E2), x ∈ sphere (0 : E2) 1 →
      ∀ z ∈ Icc a b, H (U i (x, z)) = z)
    (hVh : ∀ (i : Fin 2) (x : E2), x ∈ sphere (0 : E2) 1 →
      ∀ z ∈ Icc a b, H (V i (x, z)) = z)
    (hlevels : ∀ z ∈ Icc a b,
      (⋃ i : Fin 2, U i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        ⋃ i : Fin 2, V i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)))
    (hdis : Disjoint
      (V 0 '' (sphere (0 : E2) 1 ×ˢ Icc a b))
      (V 1 '' (sphere (0 : E2) 1 ×ˢ Icc a b))) :
    ∃ e : Equiv.Perm (Fin 2),
      (∀ i : Fin 2,
        U i '' (sphere (0 : E2) 1 ×ˢ Icc a b) =
          V (e i) '' (sphere (0 : E2) 1 ×ˢ Icc a b)) ∧
      ∀ (i : Fin 2) (z : ℝ), z ∈ Icc a b →
        U i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
          V (e i) '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
  classical
  let C : Set (E2 × ℝ) := sphere (0 : E2) 1 ×ˢ Icc a b
  let A : Fin 2 → Set E3 := fun i => U i '' C
  let B : Fin 2 → Set E3 := fun i => V i '' C
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have hC : IsConnected C :=
    (isConnected_sphere hdim (0 : E2) (by norm_num : (0 : ℝ) ≤ 1)).prod
      (isConnected_Icc hab)
  have hCcompact : IsCompact C := (isCompact_sphere (0 : E2) 1).prod isCompact_Icc
  have hA (i : Fin 2) : IsConnected (A i) := hC.image (U i) (hU i)
  have hBclosed (i : Fin 2) : IsClosed (B i) :=
    (hCcompact.image_of_continuousOn (hV i)).isClosed
  have hBne (i : Fin 2) : (B i).Nonempty := hC.nonempty.image (V i)
  have hTransfer (f g : Fin 2 → (E2 × ℝ) → E3)
      (h : ∀ z ∈ Icc a b,
        (⋃ i : Fin 2, f i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
          ⋃ i : Fin 2, g i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) :
      (⋃ i : Fin 2, f i '' C) ⊆ ⋃ i : Fin 2, g i '' C := by
    intro y hy
    rcases mem_iUnion.mp hy with ⟨i, q, hq, hqy⟩
    have hyz : y ∈ ⋃ i : Fin 2, f i '' (sphere (0 : E2) 1 ×ˢ ({q.2} : Set ℝ)) :=
      mem_iUnion.mpr ⟨i, q, ⟨hq.1, rfl⟩, hqy⟩
    rw [h q.2 hq.2] at hyz
    rcases mem_iUnion.mp hyz with ⟨k, p, hp, hpy⟩
    refine mem_iUnion.mpr ⟨k, p, ⟨hp.1, ?_⟩, hpy⟩
    simpa only [mem_singleton_iff.mp hp.2] using hq.2
  have hUnionAll : (⋃ i : Fin 2, A i) = ⋃ i : Fin 2, B i :=
    Subset.antisymm (hTransfer U V hlevels) (hTransfer V U (fun z hz => (hlevels z hz).symm))
  have hTwo (E : Fin 2 → Set E3) : (⋃ i : Fin 2, E i) = E 0 ∪ E 1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · intro hy
      exact hy.elim (fun hh => mem_iUnion.mpr ⟨0, hh⟩)
        (fun hh => mem_iUnion.mpr ⟨1, hh⟩)
  have hUnion : A 0 ∪ A 1 = B 0 ∪ B 1 := by
    simpa only [hTwo] using hUnionAll
  have hSub (i : Fin 2) : A i ⊆ B 0 ∪ B 1 := by
    intro y hy
    have hh : y ∈ ⋃ k : Fin 2, A k := mem_iUnion.mpr ⟨i, hy⟩
    rw [hUnionAll] at hh
    simpa only [hTwo] using hh
  have hChoice (i : Fin 2) : A i ⊆ B 0 ∨ A i ⊆ B 1 := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp (hA i).isPreconnected
      (B 0) (B 1) (hBclosed 0) (hBclosed 1) (hSub i)
    rw [Set.disjoint_iff_inter_eq_empty.mp hdis, inter_empty]
  have hImpossible (j k : Fin 2) (hj : Disjoint (B j) (B k))
      (h0 : A 0 ⊆ B j) (h1 : A 1 ⊆ B j) : False := by
    obtain ⟨y, hy⟩ := hBne k
    have hyAll : y ∈ ⋃ i : Fin 2, A i := by
      rw [hUnionAll]
      exact mem_iUnion.mpr ⟨k, hy⟩
    have hyUnion : y ∈ A 0 ∪ A 1 := by
      simpa only [hTwo] using hyAll
    exact Set.disjoint_left.mp hj (hyUnion.elim (fun hh => h0 hh) (fun hh => h1 hh)) hy
  have hEqual (A0 A1 B0 B1 : Set E3) (h0 : A0 ⊆ B0) (h1 : A1 ⊆ B1)
      (hu : A0 ∪ A1 = B0 ∪ B1) (hd : Disjoint B0 B1) : A0 = B0 ∧ A1 = B1 := by
    constructor
    · apply Subset.antisymm h0
      intro y hy
      have hyA : y ∈ A0 ∪ A1 := hu.symm ▸ Or.inl hy
      rcases hyA with hyA | hyA
      · exact hyA
      · exact False.elim (Set.disjoint_left.mp hd hy (h1 hyA))
    · apply Subset.antisymm h1
      intro y hy
      have hyA : y ∈ A0 ∪ A1 := hu.symm ▸ Or.inr hy
      rcases hyA with hyA | hyA
      · exact False.elim (Set.disjoint_left.mp hd (h0 hyA) hy)
      · exact hyA
  have hMatch : ∃ e : Equiv.Perm (Fin 2), ∀ i : Fin 2, A i = B (e i) := by
    rcases hChoice 0 with h00 | h01 <;> rcases hChoice 1 with h10 | h11
    · exact False.elim (hImpossible 0 1 hdis h00 h10)
    · obtain ⟨h0, h1⟩ := hEqual (A 0) (A 1) (B 0) (B 1) h00 h11 hUnion hdis
      refine ⟨Equiv.refl (Fin 2), ?_⟩
      intro i
      fin_cases i
      · exact h0
      · exact h1
    · have hu : A 0 ∪ A 1 = B 1 ∪ B 0 := hUnion.trans (union_comm _ _)
      obtain ⟨h0, h1⟩ := hEqual (A 0) (A 1) (B 1) (B 0) h01 h10 hu hdis.symm
      refine ⟨Equiv.swap 0 1, ?_⟩
      intro i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · exact False.elim (hImpossible 1 0 hdis.symm h01 h11)
  have hSlice (f : (E2 × ℝ) → E3)
      (hf : ∀ x ∈ sphere (0 : E2) 1, ∀ t ∈ Icc a b, H (f (x, t)) = t)
      (z : ℝ) (hz : z ∈ Icc a b) :
      f '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        (f '' C) ∩ {y : E3 | H y = z} := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htz : t = z := mem_singleton_iff.mp ht
      subst t
      exact ⟨⟨(x, z), ⟨hx, hz⟩, rfl⟩, hf x hx z hz⟩
    · rintro ⟨⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, hy⟩
      have htz : t = z := (hf x hx t ht).symm.trans hy
      exact ⟨(x, t), ⟨hx, htz⟩, rfl⟩
  obtain ⟨e, he⟩ := hMatch
  refine ⟨e, he, ?_⟩
  intro i z hz
  rw [hSlice (U i) (hUh i) z hz, hSlice (V (e i)) (hVh (e i)) z hz]
  change A i ∩ _ = B (e i) ∩ _
  rw [he]

end PoincareConjecture.M25.Topology3D
