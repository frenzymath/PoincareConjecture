import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalOuterCaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



def chartedHalfBlock (S : Set E) (f : E → ((ℝ × ℝ) × ℝ)) (boundary : Bool) : Set E :=
  S ∩ {x | (boundary = true → 0 ≤ (f x).1.1) ∧ 0 ≤ (f x).2}



def chartedHalfBlockOuter (L : Set E) (f : E → ((ℝ × ℝ) × ℝ))
    (boundary : Bool) : Set E := chartedHalfBlock L f boundary




def chartedHalfBlockActive (S : Set E) (f : E → ((ℝ × ℝ) × ℝ))
    (boundary : Bool) : Set E :=
  S ∩ {x | (boundary = true → 0 ≤ (f x).1.1) ∧ 0 ≤ (f x).2 ∧
    ((boundary = true ∧ (f x).1.1 = 0) ∨ (f x).2 = 0)}





theorem AffineOnFaces.conical_halfBlock_ball_pairs
    [DecidableEq E] {K : SimplicialComplex ℝ E} {f : E → ((ℝ × ℝ) × ℝ)}
    (hf : K.AffineOnFaces f) (hK : K.faces.Finite) (hinj : InjOn f K.space)
    {p : E} (hp : p ∈ K.vertices) (hstar : K.closedStar p = K) (hfp : f p = 0)
    (hint : (0 : (ℝ × ℝ) × ℝ) ∈ interior (f '' K.space))
    (c : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ)) (boundary : Bool) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (chartedHalfBlock K.space f boundary)
      (chartedHalfBlockOuter (K.link p).space f boundary ∪
        chartedHalfBlockActive K.space f boundary) ∧
    IsFinitePLBallPair (ℝ × ℝ) (chartedHalfBlockOuter (K.link p).space f boundary)
      (chartedHalfBlockOuter (K.link p).space f boundary ∩
        chartedHalfBlockActive K.space f boundary) := by
  classical
  let A : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let B : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hlinksub : (K.link p).space ⊆ K.space :=
    space_subset_of_le (fun _ hs => hs.1)
  obtain ⟨hcaps, hquads⟩ := hf.isFinitePLBallPair_conical_outer_caps hK hinj hp hfp hint c
  cases boundary
  · have hball := hf.isFinitePLBallPair_conical_halfspaces hK hinj hp hstar hfp hint c
      (fun _ : Unit => B) ⟨((0, 0), 1), fun _ => by norm_num [B]⟩
    have hbody : chartedHalfBlock K.space f false = K.space ∩ {x | 0 ≤ (f x).2} := by
      ext x
      simp [chartedHalfBlock]
    have hrim : {x | x ∈ K.space ∧ (0 ≤ (f x).2) ∧
        (x ∈ (K.link p).space ∨ (f x).2 = 0)} =
        chartedHalfBlockOuter (K.link p).space f false ∪
          chartedHalfBlockActive K.space f false := by
      ext x
      simp only [chartedHalfBlockOuter, chartedHalfBlock, chartedHalfBlockActive,
        mem_union, mem_inter_iff, mem_ofPred_eq, Bool.false_eq_true,
        false_implies, false_and, false_or, true_and]
      constructor
      · rintro ⟨hxs, hn, hl | he⟩
        · exact Or.inl ⟨hl, hn⟩
        · exact Or.inr ⟨hxs, hn, he⟩
      · rintro (⟨hl, hn⟩ | ⟨hxs, hn, he⟩)
        · exact ⟨hlinksub hl, hn, Or.inl hl⟩
        · exact ⟨hxs, hn, Or.inr he⟩
    have hcontact : chartedHalfBlockOuter (K.link p).space f false ∩
        chartedHalfBlockActive K.space f false = (K.link p).space ∩ {x | (f x).2 = 0} := by
      ext x
      simp only [chartedHalfBlockOuter, chartedHalfBlock, chartedHalfBlockActive,
        mem_inter_iff, mem_ofPred_eq, Bool.false_eq_true, false_implies,
        false_and, false_or, true_and]
      constructor
      · rintro ⟨⟨hl, _⟩, _, _, he⟩
        exact ⟨hl, he⟩
      · rintro ⟨hl, he⟩
        have hn : 0 ≤ (f x).2 := he ▸ le_rfl
        exact ⟨⟨hl, hn⟩, hlinksub hl, hn, he⟩
    refine ⟨?_, ?_⟩
    · rw [hbody, ← hrim]
      simpa [B] using hball
    · rw [hcontact]
      simpa [chartedHalfBlockOuter, chartedHalfBlock] using hcaps false
  · let F : Bool → ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := fun j => if j then B else A
    have hball := hf.isFinitePLBallPair_conical_halfspaces hK hinj hp hstar hfp hint c
      F ⟨((1, 0), 1), fun j => by cases j <;> norm_num [F, A, B]⟩
    have hbody : chartedHalfBlock K.space f true =
        K.space ∩ {x | 0 ≤ (f x).1.1 ∧ 0 ≤ (f x).2} := by
      ext x
      simp [chartedHalfBlock]
    have hrim : {x | x ∈ K.space ∧ (0 ≤ (f x).1.1 ∧ 0 ≤ (f x).2) ∧
        (x ∈ (K.link p).space ∨ (f x).1.1 = 0 ∨ (f x).2 = 0)} =
        chartedHalfBlockOuter (K.link p).space f true ∪
          chartedHalfBlockActive K.space f true := by
      ext x
      simp only [chartedHalfBlockOuter, chartedHalfBlock, chartedHalfBlockActive,
        mem_union, mem_inter_iff, mem_ofPred_eq, true_implies,
        true_and]
      constructor
      · rintro ⟨hxs, hx, hl | he⟩
        · exact Or.inl ⟨hl, hx⟩
        · exact Or.inr ⟨hxs, hx.1, hx.2, he⟩
      · rintro (⟨hl, hx⟩ | ⟨hxs, ha, hb, he⟩)
        · exact ⟨hlinksub hl, hx, Or.inl hl⟩
        · exact ⟨hxs, ⟨ha, hb⟩, Or.inr he⟩
    have hcontact : chartedHalfBlockOuter (K.link p).space f true ∩
        chartedHalfBlockActive K.space f true =
        ((K.link p).space ∩ {x | (f x).1.1 = 0 ∧ 0 ≤ (f x).2}) ∪
          ((K.link p).space ∩ {x | (f x).2 = 0 ∧ 0 ≤ (f x).1.1}) := by
      ext x
      simp only [chartedHalfBlockOuter, chartedHalfBlock, chartedHalfBlockActive,
        mem_union, mem_inter_iff, mem_ofPred_eq, true_implies,
        true_and]
      constructor
      · rintro ⟨⟨hl, ha, hb⟩, _, _, _, he | he⟩
        · exact Or.inl ⟨hl, he, hb⟩
        · exact Or.inr ⟨hl, he, ha⟩
      · rintro (⟨hl, he, hb⟩ | ⟨hl, he, ha⟩)
        · have ha : 0 ≤ (f x).1.1 := he ▸ le_rfl
          exact ⟨⟨hl, ha, hb⟩, hlinksub hl, ha, hb, Or.inl he⟩
        · have hb : 0 ≤ (f x).2 := he ▸ le_rfl
          exact ⟨⟨hl, ha, hb⟩, hlinksub hl, ha, hb, Or.inr he⟩
    refine ⟨?_, ?_⟩
    · rw [hbody, ← hrim]
      simpa [F, A, B] using hball
    · rw [hcontact]
      simpa [chartedHalfBlockOuter, chartedHalfBlock] using hquads false false






theorem AffineOnFaces.exists_conical_halfBlock_extension
    [DecidableEq E] {K : SimplicialComplex ℝ E} {f : E → ((ℝ × ℝ) × ℝ)}
    (hf : K.AffineOnFaces f) (hK : K.faces.Finite) (hinj : InjOn f K.space)
    {p : E} (hp : p ∈ K.vertices) (hstar : K.closedStar p = K) (hfp : f p = 0)
    (hint : (0 : (ℝ × ℝ) × ℝ) ∈ interior (f '' K.space))
    (c : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ)) (boundary : Bool)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {t b d q : Set Y} (ht : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) t (b ∪ d))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q) (hcontact : b ∩ d = q)
    (e : chartedHalfBlockActive K.space f boundary ≃ₜ d) (he : e.IsFinitePL)
    (hmem : ∀ x : chartedHalfBlockActive K.space f boundary,
      (x : E) ∈ chartedHalfBlockOuter (K.link p).space f boundary ↔ (e x : Y) ∈ q) :
    ∃ H : chartedHalfBlock K.space f boundary ≃ₜ t, H.IsFinitePL ∧
      (∀ (x : chartedHalfBlock K.space f boundary)
        (hx : (x : E) ∈ chartedHalfBlockActive K.space f boundary),
        (H x : Y) = e ⟨x, hx⟩) ∧
      (∀ x : chartedHalfBlock K.space f boundary,
        (x : E) ∈ chartedHalfBlockOuter (K.link p).space f boundary ↔ (H x : Y) ∈ b) ∧
      ∀ x : chartedHalfBlock K.space f boundary,
        (x : E) ∈ chartedHalfBlockActive K.space f boundary ↔ (H x : Y) ∈ d := by
  obtain ⟨hs, ho⟩ := hf.conical_halfBlock_ball_pairs hK hinj hp hstar hfp hint c boundary
  obtain ⟨H, hH, hkeep, houter, hactive⟩ :=
    hs.exists_extension_of_boundary_piece ht ho hb rfl hcontact e he (by
      intro x
      simpa only [mem_inter_iff, x.property, and_true] using hmem x)
  refine ⟨H, hH, ?_, houter, hactive⟩
  intro x hx
  exact congrArg Subtype.val (hkeep ⟨x, hx⟩)

end Geometry.SimplicialComplex
