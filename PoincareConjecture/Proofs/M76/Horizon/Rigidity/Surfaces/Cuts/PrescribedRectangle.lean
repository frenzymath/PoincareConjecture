import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.FourArcRectangle

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_rectangle_with_prescribed_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M W Z L R : Set E} {p₀ p₁ q₀ q₁ : E}
    (hM : IsFinitePLBallPair (ℝ × ℝ) M ((W ∪ Z) ∪ (L ∪ R)))
    (e₀ : I ≃ₜ W) (e₁ : I ≃ₜ Z) (d₀ : I ≃ₜ L) (d₁ : I ≃ₜ R)
    (he₀ : e₀.IsFinitePL) (he₁ : e₁.IsFinitePL)
    (hd₀ : d₀.IsFinitePL) (hd₁ : d₁.IsFinitePL)
    (he₀0 : (e₀ 0 : E) = p₀) (he₀1 : (e₀ 1 : E) = p₁)
    (he₁0 : (e₁ 0 : E) = q₀) (he₁1 : (e₁ 1 : E) = q₁)
    (hd₀0 : (d₀ 0 : E) = p₀) (hd₀1 : (d₀ 1 : E) = q₀)
    (hd₁0 : (d₁ 0 : E) = p₁) (hd₁1 : (d₁ 1 : E) = q₁)
    (hWZ : Disjoint W Z) (hLR : Disjoint L R)
    (hWL : W ∩ L = {p₀}) (hWR : W ∩ R = {p₁})
    (hZL : Z ∩ L = {q₀}) (hZR : Z ∩ R = {q₁}) :
    ∃ C : Square ≃ₜ M, C.IsFinitePL ∧
      (∀ t : I, (C ⟨(t, 0), t.property, by norm_num⟩ : E) = e₀ t) ∧
      (∀ t : I, (C ⟨(t, 1), t.property, by norm_num⟩ : E) = e₁ t) ∧
      (∀ t : I, (C ⟨(0, t), by norm_num, t.property⟩ : E) = d₀ t) ∧
      (∀ t : I, (C ⟨(1, t), by norm_num, t.property⟩ : E) = d₁ t) := by
  classical
  let A : E → ℝ := fun x ↦ if x ∈ W then 0 else if x ∈ Z then 1 else
    if hx : x ∈ L then (d₀.symm ⟨x, hx⟩ : ℝ) else
    if hx : x ∈ R then (d₁.symm ⟨x, hx⟩ : ℝ) else 0
  have hA₀ (x : I) : A (e₀ x) = 0 := by simp only [A, (e₀ x).property, if_true]
  have hA₁ (x : I) : A (e₁ x) = 1 := by
    have hn : (e₁ x : E) ∉ W := fun h ↦ disjoint_left.mp hWZ h (e₁ x).property
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
      · have hn : (d₁ x : E) ∉ L := fun h ↦ disjoint_left.mp hLR h (d₁ x).property
        simp only [A, hw, hz, if_false, hn, dite_false, (d₁ x).property,
          dite_true, d₁.symm_apply_apply]
  obtain ⟨H, hH, _, hHW, hHZ, hHL, hHR⟩ :=
    Homeomorph.exists_height_preserving_rectangle_boundary zero_lt_one
      e₀ e₁ d₀ d₁ he₀ he₁ hd₀ hd₁ A hA₀ hA₁ hAl hAr hLR
      (he₀0.trans hd₀0.symm) (he₀1.trans hd₁0.symm)
      (he₁0.trans hd₀1.symm) (he₁1.trans hd₁1.symm)
  let B : Set (ℝ × ℝ) := ((I ×ˢ {0}) ∪ (I ×ˢ {1})) ∪ (({0} ×ˢ I) ∪ ({1} ×ˢ I))
  have hSquare : IsFinitePLBallPair (ℝ × ℝ) Square B := by
    have h := (isFinitePLBallPair_Icc zero_lt_one).prod (isFinitePLBallPair_Icc zero_lt_one)
    convert h using 1
    ext x
    simp only [B, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  obtain ⟨C, hC, hCH, _⟩ := hSquare.exists_extension hM H hH
  refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (congrArg Subtype.val (hCH ⟨(t, 0), Or.inl (Or.inl ⟨t.property, rfl⟩)⟩)).trans (hHW t)
  · intro t
    exact (congrArg Subtype.val (hCH ⟨(t, 1), Or.inl (Or.inr ⟨t.property, rfl⟩)⟩)).trans (hHZ t)
  · intro t
    exact (congrArg Subtype.val (hCH ⟨(0, t), Or.inr (Or.inl ⟨rfl, t.property⟩)⟩)).trans (hHL t)
  · intro t
    exact (congrArg Subtype.val (hCH ⟨(1, t), Or.inr (Or.inr ⟨rfl, t.property⟩)⟩)).trans (hHR t)

theorem exists_rectangle_respecting_pairings
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M W Z L R : Set E} {p₀ p₁ q₀ q₁ : E}
    (hM : IsFinitePLBallPair (ℝ × ℝ) M ((W ∪ Z) ∪ (L ∪ R)))
    (hW : IsFinitePLBallPair ℝ W {p₀, p₁})
    (hL : IsFinitePLBallPair ℝ L {p₀, q₀})
    (hp : p₀ ≠ p₁) (h₀ : p₀ ≠ q₀)
    (pairW : W ≃ₜ Z) (pairL : L ≃ₜ R)
    (hpW : pairW.IsFinitePL) (hpL : pairL.IsFinitePL)
    (hW0 : (pairW ⟨p₀, hW.1 (by simp)⟩ : E) = q₀)
    (hW1 : (pairW ⟨p₁, hW.1 (by simp)⟩ : E) = q₁)
    (hL0 : (pairL ⟨p₀, hL.1 (by simp)⟩ : E) = p₁)
    (hL1 : (pairL ⟨q₀, hL.1 (by simp)⟩ : E) = q₁)
    (hWZ : Disjoint W Z) (hLR : Disjoint L R)
    (hWL : W ∩ L = {p₀}) (hWR : W ∩ R = {p₁})
    (hZL : Z ∩ L = {q₀}) (hZR : Z ∩ R = {q₁}) :
    ∃ (C : Square ≃ₜ M) (e : I ≃ₜ W) (d : I ≃ₜ L),
      C.IsFinitePL ∧ e.IsFinitePL ∧ d.IsFinitePL ∧
      (∀ t : I, (C ⟨(t, 0), t.property, by norm_num⟩ : E) = e t) ∧
      (∀ t : I, (C ⟨(t, 1), t.property, by norm_num⟩ : E) = pairW (e t)) ∧
      (∀ t : I, (C ⟨(0, t), by norm_num, t.property⟩ : E) = d t) ∧
      (∀ t : I, (C ⟨(1, t), by norm_num, t.property⟩ : E) = pairL (d t)) := by
  obtain ⟨e, he, he0, he1⟩ := hW.exists_unitInterval_chart_with_endpoints hp
  obtain ⟨d, hd, hd0, hd1⟩ := hL.exists_unitInterval_chart_with_endpoints h₀
  have he0' : e 0 = ⟨p₀, hW.1 (by simp)⟩ := Subtype.ext he0
  have he1' : e 1 = ⟨p₁, hW.1 (by simp)⟩ := Subtype.ext he1
  have hd0' : d 0 = ⟨p₀, hL.1 (by simp)⟩ := Subtype.ext hd0
  have hd1' : d 1 = ⟨q₀, hL.1 (by simp)⟩ := Subtype.ext hd1
  obtain ⟨C, hC, hw, hz, hl, hr⟩ := exists_rectangle_with_prescribed_sides hM
    e (e.trans pairW) d (d.trans pairL) he (he.trans hpW) hd (hd.trans hpL)
    he0 he1 (by simpa only [Homeomorph.trans_apply, he0'] using hW0)
    (by simpa only [Homeomorph.trans_apply, he1'] using hW1) hd0 hd1
    (by simpa only [Homeomorph.trans_apply, hd0'] using hL0)
    (by simpa only [Homeomorph.trans_apply, hd1'] using hL1)
    hWZ hLR hWL hWR hZL hZR
  exact ⟨C, e, d, hC, he, hd, hw, hz, hl, hr⟩

end PoincareConjecture.M76.OriginalTriangleCopies
