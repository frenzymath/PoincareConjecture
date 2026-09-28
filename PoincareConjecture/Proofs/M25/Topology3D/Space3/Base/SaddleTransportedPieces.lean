import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleCirclePartition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs









set_option autoImplicit false

open Set Function
open scoped Matrix

namespace PoincareConjecture.M25.Topology3D

private theorem transported_arc_disc_incidence
    {X I : Type*} (F : X → X) (hF : Injective F)
    (A L C O : Set X) (pminus pplus : I → X) (i k : I)
    (htransport : MapsTo F A (L \ O))
    (hwall : L ∩ (C \ O) = range pplus)
    (hminusC : ∀ b, pminus b ∈ C)
    (hport : ∀ b, F (pminus b) = pplus b)
    (hincidence : A ∩ C = {pminus i, pminus k}) :
    (F '' A) ∩ C = {pplus i, pplus k} := by
  have hplusC (b : I) : pplus b ∈ C := by
    have hb : pplus b ∈ L ∩ (C \ O) := by
      rw [hwall]
      exact mem_range_self b
    exact hb.2.1
  ext x
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hCa⟩
    have hEa := htransport ha
    have hwa : F a ∈ L ∩ (C \ O) := ⟨hEa.1, hCa, hEa.2⟩
    rw [hwall] at hwa
    obtain ⟨b, hb⟩ := hwa
    have hba : pminus b = a := hF ((hport b).trans hb)
    have hlow : a ∈ A ∩ C := ⟨ha, hba ▸ hminusC b⟩
    rw [hincidence] at hlow
    simp only [mem_insert_iff, mem_singleton_iff] at hlow ⊢
    rcases hlow with hi | hk
    · exact Or.inl ((congrArg F hi).trans (hport i))
    · exact Or.inr ((congrArg F hk).trans (hport k))
  · simp only [mem_insert_iff, mem_singleton_iff]
    rintro (rfl | rfl)
    · have hi : pminus i ∈ A ∩ C := by rw [hincidence]; simp
      exact ⟨⟨pminus i, hi.1, hport i⟩, hplusC i⟩
    · have hk : pminus k ∈ A ∩ C := by rw [hincidence]; simp
      exact ⟨⟨pminus k, hk.1, hport k⟩, hplusC k⟩

private theorem disjoint_unions_of_disc_incidence
    {X : Type*} (A B : Fin 2 → Set X) (C : Set X)
    (hAA : Disjoint (A 0) (A 1)) (hBB : Disjoint (B 0) (B 1))
    (hBC : ∀ b, B b ⊆ C) (hAB : ∀ b, A b ∩ C ⊆ B b) :
    Disjoint (B 0 ∪ A 0) (B 1 ∪ A 1) := by
  apply disjoint_left.mpr
  intro x hx0 hx1
  rcases hx0 with hx0 | hx0
  · rcases hx1 with hx1 | hx1
    · exact disjoint_left.mp hBB hx0 hx1
    · exact disjoint_left.mp hBB hx0 (hAB 1 ⟨hx1, hBC 0 hx0⟩)
  · rcases hx1 with hx1 | hx1
    · exact disjoint_left.mp hBB (hAB 0 ⟨hx0, hBC 1 hx1⟩) hx1
    · exact disjoint_left.mp hAA hx0 hx1

private theorem level_cover_from_disc_and_exterior
    {X : Type*} (L C O : Set X) (A B : Fin 2 → Set X)
    (hOC : O ⊆ C)
    (hlocal : L ∩ C = ⋃ b, B b)
    (hexterior : L \ O = ⋃ b, A b) :
    L = ⋃ b, B b ∪ A b := by
  classical
  have hsplit : L = (L ∩ C) ∪ (L \ O) := by
    ext x
    constructor
    · intro hx
      by_cases hC : x ∈ C
      · exact Or.inl ⟨hx, hC⟩
      · exact Or.inr ⟨hx, fun hO => hC (hOC hO)⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
  rw [hsplit, hlocal, hexterior]
  ext x
  simp only [mem_union, mem_iUnion, exists_or]




theorem exists_saddle_transported_two_pieces
    (F : E3 ≃ₜ E3) (Lm Lp C O : Set E3) (hOC : O ⊆ C)
    (pm pp : Fin 4 → E3) (ends : Fin 2 × Fin 2 ≃ Fin 4)
    (label : Fin 2 ≃ Fin 2)
    (a : Fin 2 → ℝ → E3) (g : Fin 2 → unitInterval → E3)
    (ha : ∀ i, Continuous (a i)) (hg : ∀ i, Continuous (g i))
    (haDis : Disjoint (a 0 '' Icc (0 : ℝ) 1) (a 1 '' Icc (0 : ℝ) 1))
    (hgDis : Disjoint (range (g 0)) (range (g 1)))
    (hminus : Lm \ O = ⋃ i, a i '' Icc (0 : ℝ) 1)
    (hlocal : Lp ∩ C = ⋃ i, range (g i))
    (hinc : ∀ i, (a i '' Icc (0 : ℝ) 1) ∩ C =
      {pm (ends (i, 0)), pm (ends (i, 1))})
    (hpm : ∀ i, pm i ∈ C)
    (hport : ∀ i, F (pm i) = pp i)
    (hwall : Lp ∩ (C \ O) = range pp)
    (hflow : F '' (Lm \ O) = Lp \ O)
    (hend : ∀ i, g i 0 = pp (finProdFinEquiv (i, (0 : Fin 2))) ∧
      g i 1 = pp (finProdFinEquiv ((![1, 0] : Fin 2 → Fin 2) i, (1 : Fin 2))))
    (hmatch : ∀ i, ({ends (i, 0), ends (i, 1)} : Set (Fin 4)) =
      {finProdFinEquiv (label i, (0 : Fin 2)),
        finProdFinEquiv ((![1, 0] : Fin 2 → Fin 2) (label i), (1 : Fin 2))}) :
    ∃ K : Fin 2 → Set E3,
      (∀ i, IsCompact (K i) ∧ IsConnected (K i)) ∧
      (∀ i k, i ≠ k → Disjoint (K i) (K k)) ∧
      (⋃ i, K i) = Lp := by
  classical
  let A0 : Fin 2 → Set E3 := fun i => a i '' Icc (0 : ℝ) 1
  let A : Fin 2 → Set E3 := fun b => F '' A0 (label.symm b)
  let B : Fin 2 → Set E3 := fun b => range (g b)
  have hA0 (i : Fin 2) : A0 i ⊆ Lm \ O := by
    intro x hx
    rw [hminus]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hmaps (i : Fin 2) : MapsTo F (A0 i) (Lp \ O) := by
    intro x hx
    rw [← hflow]
    exact ⟨x, hA0 i hx, rfl⟩
  have hincPlus (i : Fin 2) : (F '' A0 i) ∩ C =
      {pp (ends (i, 0)), pp (ends (i, 1))} :=
    transported_arc_disc_incidence F F.injective (A0 i) Lp C O pm pp
      (ends (i, 0)) (ends (i, 1)) (hmaps i) hwall hpm hport (hinc i)
  have hincA (b : Fin 2) : A b ∩ C = {g b 0, g b 1} := by
    have hpairs := congrArg (fun s : Set (Fin 4) => pp '' s) (hmatch (label.symm b))
    simp only [image_insert_eq, image_singleton, label.apply_symm_apply] at hpairs
    change (F '' A0 (label.symm b)) ∩ C = {g b 0, g b 1}
    rw [hincPlus, hpairs, ← (hend b).1, ← (hend b).2]
  have hBC (b : Fin 2) : B b ⊆ C := by
    intro x hx
    have hh : x ∈ ⋃ i, range (g i) := mem_iUnion.mpr ⟨b, hx⟩
    rw [← hlocal] at hh
    exact hh.2
  have hAB (b : Fin 2) : A b ∩ C ⊆ B b := by
    intro x hx
    rw [hincA b] at hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_range_self (0 : unitInterval)
    · exact mem_range_self (1 : unitInterval)
  have hA0Dis (i k : Fin 2) (hik : i ≠ k) : Disjoint (A0 i) (A0 k) := by
    fin_cases i <;> fin_cases k
    · exact False.elim (hik rfl)
    · exact haDis
    · exact haDis.symm
    · exact False.elim (hik rfl)
  have hAA : Disjoint (A 0) (A 1) := by
    apply disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
    have hne : label.symm 0 ≠ label.symm 1 :=
      fun h => zero_ne_one (label.symm.injective h)
    exact disjoint_left.mp (hA0Dis _ _ hne) hs ((F.injective hts) ▸ ht)
  have hexterior : Lp \ O = ⋃ b, A b := by
    rw [← hflow, hminus, image_iUnion]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨label i, ?_⟩
      simpa only [A, A0, label.symm_apply_apply] using hi
    · intro x hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨label.symm b, hb⟩
  let K : Fin 2 → Set E3 := fun b => B b ∪ A b
  have hKcompact (b : Fin 2) : IsCompact (K b) :=
    (isCompact_range (hg b)).union
      ((isCompact_Icc.image (ha (label.symm b))).image F.continuous)
  have hKconnected (b : Fin 2) : IsConnected (K b) := by
    have hpoint : g b 0 ∈ A b ∩ C := by rw [hincA b]; simp
    have hAconnected : IsConnected (A b) :=
      ((isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num)).image
        (a (label.symm b)) (ha (label.symm b)).continuousOn).image F F.continuous.continuousOn
    exact IsConnected.union ⟨g b 0, mem_range_self 0, hpoint.1⟩
      (isConnected_range (hg b)) hAconnected
  have hK01 : Disjoint (K 0) (K 1) :=
    disjoint_unions_of_disc_incidence A B C hAA hgDis hBC hAB
  refine ⟨K, fun b => ⟨hKcompact b, hKconnected b⟩, ?_, ?_⟩
  · intro b k hbk
    fin_cases b <;> fin_cases k
    · exact False.elim (hbk rfl)
    · exact hK01
    · exact hK01.symm
    · exact False.elim (hbk rfl)
  · exact (level_cover_from_disc_and_exterior Lp C O A B hOC hlocal hexterior).symm

end PoincareConjecture.M25.Topology3D
