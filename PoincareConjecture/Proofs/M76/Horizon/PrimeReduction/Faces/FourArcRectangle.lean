import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRectangleBoundary
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_four_arc_rectangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M W Z L R : Set E} {p₀ p₁ q₀ q₁ : E}
    (hM : IsFinitePLBallPair (ℝ × ℝ) M ((W ∪ Z) ∪ (L ∪ R)))
    (hW : IsFinitePLBallPair ℝ W {p₀, p₁})
    (hZ : IsFinitePLBallPair ℝ Z {q₀, q₁})
    (hL : IsFinitePLBallPair ℝ L {p₀, q₀})
    (hR : IsFinitePLBallPair ℝ R {p₁, q₁})
    (hp : p₀ ≠ p₁) (hq : q₀ ≠ q₁) (h₀ : p₀ ≠ q₀) (h₁ : p₁ ≠ q₁)
    (hWZ : Disjoint W Z) (hLR : Disjoint L R)
    (hWL : W ∩ L = {p₀}) (hWR : W ∩ R = {p₁})
    (hZL : Z ∩ L = {q₀}) (hZR : Z ∩ R = {q₁}) :
    ∃ C : Square ≃ₜ M, C.IsFinitePL ∧
      (∀ x, (C x : E) ∈ W ↔ (x : ℝ × ℝ).2 = 0) ∧
      (∀ x, (C x : E) ∈ Z ↔ (x : ℝ × ℝ).2 = 1) ∧
      (∀ x, (C x : E) ∈ L ↔ (x : ℝ × ℝ).1 = 0) ∧
      (∀ x, (C x : E) ∈ R ↔ (x : ℝ × ℝ).1 = 1) := by
  classical
  obtain ⟨e₀, he₀, he₀0, he₀1⟩ := hW.exists_unitInterval_chart_with_endpoints hp
  obtain ⟨e₁, he₁, he₁0, he₁1⟩ := hZ.exists_unitInterval_chart_with_endpoints hq
  obtain ⟨d₀, hd₀, hd₀0, hd₀1⟩ := hL.exists_unitInterval_chart_with_endpoints h₀
  obtain ⟨d₁, hd₁, hd₁0, hd₁1⟩ := hR.exists_unitInterval_chart_with_endpoints h₁
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
      have hx : x = 0 := d₀.injective he
      simp only [A, hw, if_true]
      exact (congrArg Subtype.val hx).symm
    · by_cases hz : (d₀ x : E) ∈ Z
      · have he : d₀ x = d₀ 1 := Subtype.ext ((hZL.subset ⟨hz, (d₀ x).property⟩).trans hd₀1.symm)
        have hx : x = 1 := d₀.injective he
        simp only [A, hw, if_false, hz, if_true]
        exact (congrArg Subtype.val hx).symm
      · simp only [A, hw, hz, if_false, (d₀ x).property, dite_true,
          d₀.symm_apply_apply]
  have hAr (x : I) : A (d₁ x) = (x : ℝ) := by
    by_cases hw : (d₁ x : E) ∈ W
    · have he : d₁ x = d₁ 0 := Subtype.ext ((hWR.subset ⟨hw, (d₁ x).property⟩).trans hd₁0.symm)
      have hx : x = 0 := d₁.injective he
      simp only [A, hw, if_true]
      exact (congrArg Subtype.val hx).symm
    · by_cases hz : (d₁ x : E) ∈ Z
      · have he : d₁ x = d₁ 1 := Subtype.ext ((hZR.subset ⟨hz, (d₁ x).property⟩).trans hd₁1.symm)
        have hx : x = 1 := d₁.injective he
        simp only [A, hw, if_false, hz, if_true]
        exact (congrArg Subtype.val hx).symm
      · have hn : (d₁ x : E) ∉ L := fun h => disjoint_left.mp hLR h (d₁ x).property
        simp only [A, hw, hz, if_false, hn, dite_false, (d₁ x).property,
          dite_true, d₁.symm_apply_apply]
  obtain ⟨H, hH, _, hHW, hHZ, hHL, hHR⟩ :=
    Homeomorph.exists_height_preserving_rectangle_boundary (show (0 : ℝ) < 1 by norm_num)
      e₀ e₁ d₀ d₁ he₀ he₁ hd₀ hd₁ A hA₀ hA₁ hAl hAr hLR
      (he₀0.trans hd₀0.symm) (he₀1.trans hd₁0.symm)
      (he₁0.trans hd₀1.symm) (he₁1.trans hd₁1.symm)
  let B : Set (ℝ × ℝ) := ((I ×ˢ {0}) ∪ (I ×ˢ {1})) ∪ (({0} ×ˢ I) ∪ ({1} ×ˢ I))
  have hSquare : IsFinitePLBallPair (ℝ × ℝ) Square B := by
    have h := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num))
    convert h using 1
    ext x
    simp only [B, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  obtain ⟨C, hC, hCH, _⟩ := hSquare.exists_extension hM H hH
  have hw (t : I) : (C ⟨(t, 0), t.property, ⟨le_rfl, zero_le_one⟩⟩ : E) = e₀ t := by
    exact (congrArg Subtype.val (hCH ⟨(t, 0), Or.inl (Or.inl ⟨t.property, rfl⟩)⟩)).trans (hHW t)
  have hz (t : I) : (C ⟨(t, 1), t.property, ⟨zero_le_one, le_rfl⟩⟩ : E) = e₁ t := by
    exact (congrArg Subtype.val (hCH ⟨(t, 1), Or.inl (Or.inr ⟨t.property, rfl⟩)⟩)).trans (hHZ t)
  have hl (t : I) : (C ⟨(0, t), ⟨le_rfl, zero_le_one⟩, t.property⟩ : E) = d₀ t := by
    exact (congrArg Subtype.val (hCH ⟨(0, t), Or.inr (Or.inl ⟨rfl, t.property⟩)⟩)).trans (hHL t)
  have hr (t : I) : (C ⟨(1, t), ⟨zero_le_one, le_rfl⟩, t.property⟩ : E) = d₁ t := by
    exact (congrArg Subtype.val (hCH ⟨(1, t), Or.inr (Or.inr ⟨rfl, t.property⟩)⟩)).trans (hHR t)
  refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := e₀.surjective ⟨C x, hx⟩
      have he := C.injective (Subtype.ext ((hw t).trans (congrArg Subtype.val ht)))
      exact (congrArg (fun z : Square => (z : ℝ × ℝ).2) he).symm
    · intro hx
      have he : x = ⟨((x : ℝ × ℝ).1, 0), x.property.1, ⟨le_rfl, zero_le_one⟩⟩ :=
        Subtype.ext (Prod.ext rfl hx)
      rw [he]
      exact (hw ⟨_, x.property.1⟩).symm ▸ (e₀ ⟨_, x.property.1⟩).property
  · intro x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := e₁.surjective ⟨C x, hx⟩
      have he := C.injective (Subtype.ext ((hz t).trans (congrArg Subtype.val ht)))
      exact (congrArg (fun z : Square => (z : ℝ × ℝ).2) he).symm
    · intro hx
      have he : x = ⟨((x : ℝ × ℝ).1, 1), x.property.1, ⟨zero_le_one, le_rfl⟩⟩ :=
        Subtype.ext (Prod.ext rfl hx)
      rw [he]
      exact (hz ⟨_, x.property.1⟩).symm ▸ (e₁ ⟨_, x.property.1⟩).property
  · intro x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := d₀.surjective ⟨C x, hx⟩
      have he := C.injective (Subtype.ext ((hl t).trans (congrArg Subtype.val ht)))
      exact (congrArg (fun z : Square => (z : ℝ × ℝ).1) he).symm
    · intro hx
      have he : x = ⟨(0, (x : ℝ × ℝ).2), ⟨le_rfl, zero_le_one⟩, x.property.2⟩ :=
        Subtype.ext (Prod.ext hx rfl)
      rw [he]
      exact (hl ⟨_, x.property.2⟩).symm ▸ (d₀ ⟨_, x.property.2⟩).property
  · intro x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := d₁.surjective ⟨C x, hx⟩
      have he := C.injective (Subtype.ext ((hr t).trans (congrArg Subtype.val ht)))
      exact (congrArg (fun z : Square => (z : ℝ × ℝ).1) he).symm
    · intro hx
      have he : x = ⟨(1, (x : ℝ × ℝ).2), ⟨zero_le_one, le_rfl⟩, x.property.2⟩ :=
        Subtype.ext (Prod.ext hx rfl)
      rw [he]
      exact (hr ⟨_, x.property.2⟩).symm ▸ (d₁ ⟨_, x.property.2⟩).property

end PoincareConjecture.M76
