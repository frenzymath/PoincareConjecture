import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGraphExtension











set_option autoImplicit false

open Set Geometry

namespace Set




theorem four_disk_graph_contacts {X : Type*} (U S : Bool × Bool → Set X)
    (hS : ∀ i, U (false, i.2) ∪ U (true, i.1) ⊆ S i)
    (hSi : Pairwise (fun i j => S i ∩ S j ⊆ U (false, i.2) ∪ U (true, i.1))) :
    (∀ i, S i ∩ (⋃ j, U j) = U (false, i.2) ∪ U (true, i.1)) ∧
      Pairwise (fun i j => S i ∩ S j ⊆ ⋃ j, U j) ∧
      (⋃ j, U j) ⊆ ⋃ i, S i := by
  have hrim (i : Bool × Bool) : U (false, i.2) ∪ U (true, i.1) ⊆ ⋃ j, U j := by
    intro x hx
    exact hx.elim (fun h => mem_iUnion.mpr ⟨(false, i.2), h⟩)
      (fun h => mem_iUnion.mpr ⟨(true, i.1), h⟩)
  refine ⟨?_, fun i j hij => (hSi hij).trans (hrim i), ?_⟩
  · intro i
    apply Subset.antisymm
    · rintro x ⟨hxi, hxU⟩
      obtain ⟨⟨k, l⟩, hxl⟩ := mem_iUnion.mp hxU
      cases k with
      | false =>
        by_cases hi : i = (false, l)
        · subst i
          exact Or.inl hxl
        · exact hSi hi ⟨hxi, hS (false, l) (Or.inl hxl)⟩
      | true =>
        by_cases hi : i = (l, false)
        · subst i
          exact Or.inr hxl
        · exact hSi hi ⟨hxi, hS (l, false) (Or.inr hxl)⟩
    · exact fun x hx => ⟨hS i hx, hrim i hx⟩
  · intro x hx
    obtain ⟨⟨k, l⟩, hxl⟩ := mem_iUnion.mp hx
    cases k with
    | false => exact mem_iUnion.mpr ⟨(false, l), hS (false, l) (Or.inl hxl)⟩
    | true => exact mem_iUnion.mpr ⟨(l, false), hS (l, false) (Or.inr hxl)⟩

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem exists_finitePL_four_disk_gluing
    (A D : Bool × Bool → Set E) (B T : Bool × Bool → Set F)
    {a b : E} {c d : F} (hab : a ≠ b) (hcd : c ≠ d)
    (hA : ∀ i, IsFinitePLBallPair ℝ (A i) {a, b})
    (hB : ∀ i, IsFinitePLBallPair ℝ (B i) {c, d})
    (hAi : Pairwise (fun i j => A i ∩ A j = {a, b}))
    (hBi : Pairwise (fun i j => B i ∩ B j = {c, d}))
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (A (false, i.2) ∪ A (true, i.1)))
    (hT : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (T i) (B (false, i.2) ∪ B (true, i.1)))
    (hDi : Pairwise (fun i j => D i ∩ D j ⊆ A (false, i.2) ∪ A (true, i.1)))
    (hTi : Pairwise (fun i j => T i ∩ T j ⊆ B (false, i.2) ∪ B (true, i.1))) :
    ∃ H : (⋃ i, D i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i (x : ⋃ i, D i), (x : E) ∈ D i ↔ (H x : F) ∈ T i) ∧
      (∀ i (x : ⋃ i, D i), (x : E) ∈ A i ↔ (H x : F) ∈ B i) ∧
      (∀ x : ⋃ i, D i, (H x : F) = c ↔ (x : E) = a) ∧
      (∀ x : ⋃ i, D i, (H x : F) = d ↔ (x : E) = b) := by
  obtain ⟨hDgraph, hDpair, hAD⟩ := four_disk_graph_contacts A D (fun i => (hD i).1) hDi
  obtain ⟨hTgraph, hTpair, hBT⟩ := four_disk_graph_contacts B T (fun i => (hT i).1) hTi
  obtain ⟨e, he, heArc, hea, heb⟩ := exists_finitePL_marked_graph A B hA hB hab hcd hAi hBi
  have hmem (i : Bool × Bool) (x : ⋃ j, A j) :
      (x : E) ∈ A (false, i.2) ∪ A (true, i.1) ↔
        (e x : F) ∈ B (false, i.2) ∪ B (true, i.1) :=
    or_congr (heArc (false, i.2) x) (heArc (true, i.1) x)
  obtain ⟨H, hH, hkeep, hpieces⟩ := IsFinitePLBallPair.exists_iUnion_extension_of_graph
    D (fun i => A (false, i.2) ∪ A (true, i.1))
    T (fun i => B (false, i.2) ∪ B (true, i.1))
    hD hT hDgraph hTgraph hDpair hTpair hAD hBT e he hmem
  have hgraph := H.mem_subset_iff_of_extension e hAD hBT hkeep
  have hval (x : ⋃ j, A j) : (H ⟨x, hAD x.property⟩ : F) = e x :=
    congrArg Subtype.val (hkeep x)
  have hArcs (i : Bool × Bool) (x : ⋃ j, D j) : (x : E) ∈ A i ↔ (H x : F) ∈ B i := by
    constructor
    · intro hxi
      have hxg : (x : E) ∈ ⋃ j, A j := mem_iUnion.mpr ⟨i, hxi⟩
      have hyi := (heArc i ⟨x, hxg⟩).mp hxi
      rwa [← hval] at hyi
    · intro hyi
      have hyg : (H x : F) ∈ ⋃ j, B j := mem_iUnion.mpr ⟨i, hyi⟩
      have hxg := (hgraph x).mpr hyg
      apply (heArc i ⟨x, hxg⟩).mpr
      rwa [← hval]
  have haG : a ∈ ⋃ j, A j := mem_iUnion.mpr ⟨(false, false), (hA _).1 (by simp)⟩
  have hbG : b ∈ ⋃ j, A j := mem_iUnion.mpr ⟨(false, false), (hA _).1 (by simp)⟩
  have haH : (H ⟨a, hAD haG⟩ : F) = c :=
    (hval ⟨a, haG⟩).trans ((hea ⟨a, haG⟩).mpr rfl)
  have hbH : (H ⟨b, hAD hbG⟩ : F) = d :=
    (hval ⟨b, hbG⟩).trans ((heb ⟨b, hbG⟩).mpr rfl)
  refine ⟨H, hH, hpieces, hArcs, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      exact congrArg Subtype.val (H.injective (Subtype.ext (hx.trans haH.symm)))
    · intro hx
      have h : x = ⟨a, hAD haG⟩ := Subtype.ext hx
      simpa only [h] using haH
  · intro x
    constructor
    · intro hx
      exact congrArg Subtype.val (H.injective (Subtype.ext (hx.trans hbH.symm)))
    · intro hx
      have h : x = ⟨b, hAD hbG⟩ := Subtype.ext hx
      simpa only [h] using hbH

end Set
