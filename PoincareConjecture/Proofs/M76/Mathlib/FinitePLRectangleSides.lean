import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem IsFinitePL.exists_horizontal_interval_chart
    {a b : ℝ} {s : Set E} {e : Icc a b ≃ₜ s} (he : e.IsFinitePL) (c : ℝ) :
    ∃ d : (Icc a b ×ˢ {c} : Set (ℝ × ℝ)) ≃ₜ s, d.IsFinitePL ∧
      ∀ x, (d x : E) = e ⟨(x : ℝ × ℝ).1, x.property.1⟩ := by
  have hcopy := he
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hcopy
  let f : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ c)
  have hf : FinitePiecewiseAffineOn f (Icc a b) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine f⟩
  have hinj : InjOn f (Icc a b) := by
    intro x _ y _ h
    exact congrArg Prod.fst h
  have himage : f '' Icc a b = Icc a b ×ˢ {c} := by
    change (fun x : ℝ => (x, c)) '' Icc a b = Icc a b ×ˢ {c}
    exact (prod_singleton (s := Icc a b) (b := c)).symm
  have hex := hf.exists_homeomorph_image hinj
  rw [himage] at hex
  obtain ⟨F, hF, hFval⟩ := hex
  refine ⟨F.symm.trans e, hF.symm.trans he, ?_⟩
  intro z
  let x : Icc a b := ⟨(z : ℝ × ℝ).1, z.property.1⟩
  have hz : F x = z := by
    apply Subtype.ext
    rw [hFval]
    exact Prod.ext rfl z.property.2.symm
  have hinv : F.symm z = x := by rw [← hz, F.symm_apply_apply]
  change (e (F.symm z) : E) = e x
  rw [hinv]




theorem IsFinitePL.exists_vertical_interval_chart
    {a b : ℝ} {s : Set E} {e : Icc a b ≃ₜ s} (he : e.IsFinitePL) (c : ℝ) :
    ∃ d : ({c} ×ˢ Icc a b : Set (ℝ × ℝ)) ≃ₜ s, d.IsFinitePL ∧
      ∀ x, (d x : E) = e ⟨(x : ℝ × ℝ).2, x.property.2⟩ := by
  have hcopy := he
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hcopy
  let f : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ c).prod (ContinuousAffineMap.id ℝ ℝ)
  have hf : FinitePiecewiseAffineOn f (Icc a b) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine f⟩
  have hinj : InjOn f (Icc a b) := by
    intro x _ y _ h
    exact congrArg Prod.snd h
  have himage : f '' Icc a b = {c} ×ˢ Icc a b := by
    change (fun x : ℝ => (c, x)) '' Icc a b = {c} ×ˢ Icc a b
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨rfl, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x.2, hy, Prod.ext hx.symm rfl⟩
  have hex := hf.exists_homeomorph_image hinj
  rw [himage] at hex
  obtain ⟨F, hF, hFval⟩ := hex
  refine ⟨F.symm.trans e, hF.symm.trans he, ?_⟩
  intro z
  let x : Icc a b := ⟨(z : ℝ × ℝ).2, z.property.2⟩
  have hz : F x = z := by
    apply Subtype.ext
    rw [hFval]
    exact Prod.ext z.property.1.symm rfl
  have hinv : F.symm z = x := by rw [← hz, F.symm_apply_apply]
  change (e (F.symm z) : E) = e x
  rw [hinv]





theorem mem_side_iff_of_height {Y : Type*} [TopologicalSpace Y]
    {I J : Set ℝ} {s t : Set Y}
    (e : I ≃ₜ s) (d : J ≃ₜ t) (A : Y → ℝ) (x₀ : I) (y₀ : J)
    (he : ∀ x : I, A (e x) = (y₀ : ℝ))
    (hd : ∀ y : J, A (d y) = (y : ℝ))
    (hmatch : (e x₀ : Y) = d y₀) (x : I) :
    (e x : Y) ∈ t ↔ x = x₀ := by
  constructor
  · intro hx
    let y := d.symm ⟨e x, hx⟩
    have hy : (d y : Y) = e x :=
      congrArg Subtype.val (d.apply_symm_apply ⟨e x, hx⟩)
    have hyy : y = y₀ := by
      apply Subtype.ext
      exact (hd y).symm.trans ((congrArg A hy).trans (he x))
    apply e.injective
    apply Subtype.ext
    rw [hyy] at hy
    exact hy.symm.trans hmatch.symm
  · rintro rfl
    rw [hmatch]
    exact (d y₀).property

end Homeomorph
