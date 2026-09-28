import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem restricted_chart_mem
    (B : OpenPartialHomeomorph V3 V3) (hB : B ∈ piecewiseAffineGroupoid V3)
    (U : Set V3) (hU : IsOpen U) :
    B.restrOpen U hU ∈ piecewiseAffineGroupoid V3 := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  exact ((mem_piecewiseAffineGroupoid_iff_forward B).mp hB).mono
    (B.restrOpen U hU).open_source inter_subset_left





theorem exists_capped_paired_chart_family
    (A R : Set V3) (D : Fin 2 → Set V3) (p : Fin 2 → V3)
    (W : Set V3) (hW : IsOpen W) (hAW : A ⊆ W) (hAR : A ⊆ R)
    (hisolate : ∀ x ∈ W, x ∈ A ↔ x ∈ D 0 ∧ x ∈ D 1)
    (B : Fin 2 → OpenPartialHomeomorph V3 V3)
    (hB : ∀ i, B i ∈ piecewiseAffineGroupoid V3)
    (V : Fin 2 → Set V3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (hVB : ∀ i, V i ⊆ (B i).source)
    (hregion : ∀ i x, x ∈ V i → (x ∈ R ↔ 0 ≤ B i x 2))
    (hfront : ∀ i x, x ∈ V i → (x ∈ frontier R ↔ B i x 2 = 0))
    (htriangle : ∀ i x, x ∈ (B i).source →
      (x ∈ D 0 ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2))
    (hsphere : ∀ i x, x ∈ (B i).source → (x ∈ D 1 ↔ B i x 1 = 0))
    (hinterior : A \ {p 0, p 1} ⊆ interior R)
    (C : ↥(A \ {p 0, p 1}) → OpenPartialHomeomorph V3 V3)
    (hC : ∀ q, C q ∈ piecewiseAffineGroupoid V3)
    (hqC : ∀ q, (q : V3) ∈ (C q).source)
    (hcross : ∀ q i x, x ∈ (C q).source → (x ∈ D i ↔ C q x i.castSucc = 0)) :
    ∃ G : A → OpenPartialHomeomorph V3 V3, ∀ q,
      (q : V3) ∈ (G q).source ∧ (G q).source ⊆ W ∧
      G q ∈ piecewiseAffineGroupoid V3 ∧
      (∀ x ∈ (G q).source,
        x ∈ A ↔ x ∈ R ∧ G q x 0 = 0 ∧ G q x 1 = 0) ∧
      (∀ i x, x ∈ (G q).source →
        (x ∈ R ∩ D i ↔ x ∈ R ∧ G q x i.castSucc = 0)) ∧
      ((G q).source ⊆ interior R ∨
        (∀ x ∈ (G q).source, x ∈ R ↔ 0 ≤ G q x 2) ∧
        (∀ x ∈ (G q).source, x ∈ frontier R ↔ G q x 2 = 0)) := by
  classical
  have haxis (G : OpenPartialHomeomorph V3 V3) (hGW : G.source ⊆ W)
      (hGD : ∀ i x, x ∈ G.source → (x ∈ R ∩ D i ↔ x ∈ R ∧ G x i.castSucc = 0)) :
      ∀ x ∈ G.source, x ∈ A ↔ x ∈ R ∧ G x 0 = 0 ∧ G x 1 = 0 := by
    intro x hx
    constructor
    · intro hxA
      have hxD := (hisolate x (hGW hx)).mp hxA
      exact ⟨hAR hxA, ((hGD 0 x hx).mp ⟨hAR hxA, hxD.1⟩).2,
        ((hGD 1 x hx).mp ⟨hAR hxA, hxD.2⟩).2⟩
    · rintro ⟨hxR, hx0, hx1⟩
      exact (hisolate x (hGW hx)).mpr
        ⟨((hGD 0 x hx).mpr ⟨hxR, hx0⟩).2, ((hGD 1 x hx).mpr ⟨hxR, hx1⟩).2⟩
  suffices hpoint : ∀ q : A, ∃ G : OpenPartialHomeomorph V3 V3,
      (q : V3) ∈ G.source ∧ G.source ⊆ W ∧ G ∈ piecewiseAffineGroupoid V3 ∧
      (∀ i x, x ∈ G.source → (x ∈ R ∩ D i ↔ x ∈ R ∧ G x i.castSucc = 0)) ∧
      (G.source ⊆ interior R ∨
        (∀ x ∈ G.source, x ∈ R ↔ 0 ≤ G x 2) ∧
        (∀ x ∈ G.source, x ∈ frontier R ↔ G x 2 = 0)) by
    choose G hq hGW hGPL hGD hGR using hpoint
    exact ⟨G, fun q => ⟨hq q, hGW q, hGPL q, haxis (G q) (hGW q) (hGD q), hGD q, hGR q⟩⟩
  have hend (q : A) (i : Fin 2) (hqi : (q : V3) = p i) :
      ∃ G : OpenPartialHomeomorph V3 V3,
      (q : V3) ∈ G.source ∧ G.source ⊆ W ∧ G ∈ piecewiseAffineGroupoid V3 ∧
      (∀ j x, x ∈ G.source → (x ∈ R ∩ D j ↔ x ∈ R ∧ G x j.castSucc = 0)) ∧
      (G.source ⊆ interior R ∨
        (∀ x ∈ G.source, x ∈ R ↔ 0 ≤ G x 2) ∧
        (∀ x ∈ G.source, x ∈ frontier R ↔ G x 2 = 0)) := by
    let G := (B i).restrOpen (V i ∩ W) ((hV i).inter hW)
    have hqV : (q : V3) ∈ V i := hqi.symm ▸ hpV i
    refine ⟨G, ⟨hVB i hqV, hqV, hAW q.property⟩, fun _ hx => hx.2.2,
      restricted_chart_mem (B i) (hB i) _ _, ?_, Or.inr ?_⟩
    · intro j x hx
      fin_cases j
      · change (x ∈ R ∧ x ∈ D 0) ↔ x ∈ R ∧ B i x 0 = 0
        rw [htriangle i x hx.1]
        exact ⟨fun hh => ⟨hh.1, hh.2.1⟩,
          fun hh => ⟨hh.1, hh.2, (hregion i x hx.2.1).mp hh.1⟩⟩
      · change (x ∈ R ∧ x ∈ D 1) ↔ x ∈ R ∧ B i x 1 = 0
        rw [hsphere i x hx.1]
    · exact ⟨fun x hx => hregion i x hx.2.1, fun x hx => hfront i x hx.2.1⟩
  intro q
  by_cases hq0 : (q : V3) = p 0
  · exact hend q 0 hq0
  by_cases hq1 : (q : V3) = p 1
  · exact hend q 1 hq1
  have hqmid : (q : V3) ∈ A \ {p 0, p 1} :=
    ⟨q.property, by simp only [mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨hq0, hq1⟩⟩
  let q' : ↥(A \ {p 0, p 1}) := ⟨q, hqmid⟩
  let G := (C q').restrOpen (interior R ∩ W) (isOpen_interior.inter hW)
  refine ⟨G, ⟨hqC q', hinterior hqmid, hAW q.property⟩, fun _ hx => hx.2.2,
    restricted_chart_mem (C q') (hC q') _ _, ?_, Or.inl (fun _ hx => hx.2.1)⟩
  intro i x hx
  change (x ∈ R ∧ x ∈ D i) ↔ x ∈ R ∧ C q' x i.castSucc = 0
  rw [hcross q' i x hx.1]

end PoincareConjecture.M76
