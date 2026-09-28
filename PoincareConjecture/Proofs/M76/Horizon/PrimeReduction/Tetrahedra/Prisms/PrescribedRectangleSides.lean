import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.FourArcRectangle









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem vertical_side_iff_of_square_chart
    {E : Type*} [TopologicalSpace E] {M L : Set E}
    (G : Square ≃ₜ M) (d : I ≃ₜ L) (k : I)
    (hside : ∀ t : I, (G ⟨(k, t), k.property, t.property⟩ : E) = d t) :
    ∀ p, (G p : E) ∈ L ↔ (p : ℝ × ℝ).1 = k := by
  intro p
  constructor
  · intro hp
    obtain ⟨t, ht⟩ := d.surjective ⟨G p, hp⟩
    have he := G.injective (Subtype.ext ((hside t).trans (congrArg Subtype.val ht)))
    exact (congrArg (fun x : Square => (x : ℝ × ℝ).1) he).symm
  · intro hp
    have he : p = ⟨(k, (p : ℝ × ℝ).2), k.property, p.property.2⟩ :=
      Subtype.ext (Prod.ext hp rfl)
    rw [he]
    exact (hside ⟨_, p.property.2⟩).symm ▸ (d ⟨_, p.property.2⟩).property

theorem horizontal_side_iff_of_square_chart
    {E : Type*} [TopologicalSpace E] {M W : Set E}
    (G : Square ≃ₜ M) (d : I ≃ₜ W) (k : I)
    (hside : ∀ t : I, (G ⟨(t, k), t.property, k.property⟩ : E) = d t) :
    ∀ p, (G p : E) ∈ W ↔ (p : ℝ × ℝ).2 = k := by
  intro p
  constructor
  · intro hp
    obtain ⟨t, ht⟩ := d.surjective ⟨G p, hp⟩
    have he := G.injective (Subtype.ext ((hside t).trans (congrArg Subtype.val ht)))
    exact (congrArg (fun x : Square => (x : ℝ × ℝ).2) he).symm
  · intro hp
    have he : p = ⟨((p : ℝ × ℝ).1, k), p.property.1, k.property⟩ :=
      Subtype.ext (Prod.ext rfl hp)
    rw [he]
    exact (hside ⟨_, p.property.1⟩).symm ▸ (d ⟨_, p.property.1⟩).property

theorem exists_rectangle_with_prescribed_vertical_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M W Z L R : Set E} {p₀ p₁ q₀ q₁ : E}
    (hM : IsFinitePLBallPair (ℝ × ℝ) M ((W ∪ Z) ∪ (L ∪ R)))
    (hW : IsFinitePLBallPair ℝ W {p₀, p₁})
    (hZ : IsFinitePLBallPair ℝ Z {q₀, q₁})
    (hp : p₀ ≠ p₁) (hq : q₀ ≠ q₁)
    (d₀ : I ≃ₜ L) (d₁ : I ≃ₜ R) (hd₀ : d₀.IsFinitePL) (hd₁ : d₁.IsFinitePL)
    (hd₀0 : (d₀ 0 : E) = p₀) (hd₀1 : (d₀ 1 : E) = q₀)
    (hd₁0 : (d₁ 0 : E) = p₁) (hd₁1 : (d₁ 1 : E) = q₁)
    (hWZ : Disjoint W Z) (hLR : Disjoint L R)
    (hWL : W ∩ L = {p₀}) (hWR : W ∩ R = {p₁})
    (hZL : Z ∩ L = {q₀}) (hZR : Z ∩ R = {q₁}) :
    ∃ C : Square ≃ₜ M, C.IsFinitePL ∧
      (∀ t : I, (C ⟨(0, t), ⟨le_rfl, zero_le_one⟩, t.property⟩ : E) = d₀ t) ∧
      (∀ t : I, (C ⟨(1, t), ⟨zero_le_one, le_rfl⟩, t.property⟩ : E) = d₁ t) ∧
      (∀ x, (C x : E) ∈ W ↔ (x : ℝ × ℝ).2 = 0) ∧
      (∀ x, (C x : E) ∈ Z ↔ (x : ℝ × ℝ).2 = 1) ∧
      (∀ x, (C x : E) ∈ L ↔ (x : ℝ × ℝ).1 = 0) ∧
      (∀ x, (C x : E) ∈ R ↔ (x : ℝ × ℝ).1 = 1) := by
  classical
  obtain ⟨e₀, he₀, he₀0, he₀1⟩ := hW.exists_unitInterval_chart_with_endpoints hp
  obtain ⟨e₁, he₁, he₁0, he₁1⟩ := hZ.exists_unitInterval_chart_with_endpoints hq
  let A : E → ℝ := fun x => if x ∈ W then 0 else if x ∈ Z then 1 else
    if hx : x ∈ L then (d₀.symm ⟨x, hx⟩ : ℝ) else
    if hx : x ∈ R then (d₁.symm ⟨x, hx⟩ : ℝ) else 0
  have hA₀ (x : I) : A (e₀ x) = 0 := by simp only [A, (e₀ x).property, if_true]
  have hA₁ (x : I) : A (e₁ x) = 1 := by
    have hn : (e₁ x : E) ∉ W := fun h => disjoint_left.mp hWZ h (e₁ x).property
    simp only [A, hn, if_false, (e₁ x).property, if_true]
  have hAl (x : I) : A (d₀ x) = (x : ℝ) := by
    by_cases hw : (d₀ x : E) ∈ W
    · have he : d₀ x = d₀ 0 := Subtype.ext ((hWL.subset ⟨hw, (d₀ x).property⟩).trans hd₀0.symm)
      have hx := d₀.injective he
      simp only [A, hw, if_true]
      exact (congrArg Subtype.val hx).symm
    · by_cases hz : (d₀ x : E) ∈ Z
      · have he : d₀ x = d₀ 1 := Subtype.ext ((hZL.subset ⟨hz, (d₀ x).property⟩).trans hd₀1.symm)
        have hx := d₀.injective he
        simp only [A, hw, if_false, hz, if_true]
        exact (congrArg Subtype.val hx).symm
      · simp only [A, hw, hz, if_false, (d₀ x).property, dite_true, d₀.symm_apply_apply]
  have hAr (x : I) : A (d₁ x) = (x : ℝ) := by
    by_cases hw : (d₁ x : E) ∈ W
    · have he : d₁ x = d₁ 0 := Subtype.ext ((hWR.subset ⟨hw, (d₁ x).property⟩).trans hd₁0.symm)
      have hx := d₁.injective he
      simp only [A, hw, if_true]
      exact (congrArg Subtype.val hx).symm
    · by_cases hz : (d₁ x : E) ∈ Z
      · have he : d₁ x = d₁ 1 := Subtype.ext ((hZR.subset ⟨hz, (d₁ x).property⟩).trans hd₁1.symm)
        have hx := d₁.injective he
        simp only [A, hw, if_false, hz, if_true]
        exact (congrArg Subtype.val hx).symm
      · have hn : (d₁ x : E) ∉ L := fun h => disjoint_left.mp hLR h (d₁ x).property
        simp only [A, hw, hz, if_false, hn, dite_false, (d₁ x).property, dite_true, d₁.symm_apply_apply]
  obtain ⟨H, hH, _, hHW, hHZ, hHL, hHR⟩ :=
    Homeomorph.exists_height_preserving_rectangle_boundary zero_lt_one e₀ e₁ d₀ d₁
      he₀ he₁ hd₀ hd₁ A hA₀ hA₁ hAl hAr hLR
      (he₀0.trans hd₀0.symm) (he₀1.trans hd₁0.symm)
      (he₁0.trans hd₀1.symm) (he₁1.trans hd₁1.symm)
  let B : Set (ℝ × ℝ) := ((I ×ˢ {0}) ∪ (I ×ˢ {1})) ∪ (({0} ×ˢ I) ∪ ({1} ×ˢ I))
  have hSquare : IsFinitePLBallPair (ℝ × ℝ) Square B := by
    have h := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).prod
      (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
    convert h using 1
    ext x
    simp only [B, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  obtain ⟨C, hC, hCH, _⟩ := hSquare.exists_extension hM H hH
  have hw (t : I) : (C ⟨(t, 0), t.property, ⟨le_rfl, zero_le_one⟩⟩ : E) = e₀ t :=
    (congrArg Subtype.val (hCH ⟨(t, 0), Or.inl (Or.inl ⟨t.property, rfl⟩)⟩)).trans (hHW t)
  have hz (t : I) : (C ⟨(t, 1), t.property, ⟨zero_le_one, le_rfl⟩⟩ : E) = e₁ t :=
    (congrArg Subtype.val (hCH ⟨(t, 1), Or.inl (Or.inr ⟨t.property, rfl⟩)⟩)).trans (hHZ t)
  have hl (t : I) : (C ⟨(0, t), ⟨le_rfl, zero_le_one⟩, t.property⟩ : E) = d₀ t :=
    (congrArg Subtype.val (hCH ⟨(0, t), Or.inr (Or.inl ⟨rfl, t.property⟩)⟩)).trans (hHL t)
  have hr (t : I) : (C ⟨(1, t), ⟨zero_le_one, le_rfl⟩, t.property⟩ : E) = d₁ t :=
    (congrArg Subtype.val (hCH ⟨(1, t), Or.inr (Or.inr ⟨rfl, t.property⟩)⟩)).trans (hHR t)
  exact ⟨C, hC, hl, hr, horizontal_side_iff_of_square_chart C e₀ 0 hw,
    horizontal_side_iff_of_square_chart C e₁ 1 hz, vertical_side_iff_of_square_chart C d₀ 0 hl,
    vertical_side_iff_of_square_chart C d₁ 1 hr⟩

end PoincareConjecture.M76
