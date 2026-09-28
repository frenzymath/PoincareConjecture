import PoincareConjecture.Proofs.M76.Mathlib.CommonCollarBandRestriction










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem IsFinitePL.exists_terminal_collarBand_comparison
    {B : Set E} {T₀ T₁ R : Set F} {lower₀ lower₁ upper : E → ℝ}
    {C₀ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₀ p.1) (upper p.1)} ≃ₜ T₀}
    {C₁ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₁ p.1) (upper p.1)} ≃ₜ T₁}
    (hC₀ : C₀.IsFinitePL) (hC₁ : C₁.IsFinitePL) (A : F →ᵃ[ℝ] ℝ)
    (hheight₀ : ∀ p, A (C₀ p) = (p : E × ℝ).2)
    (hheight₁ : ∀ p, A (C₁ p) = (p : E × ℝ).2)
    (hcontact₀ : ∀ p, (C₀ p : F) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hcontact₁ : ∀ p, (C₁ p : F) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hagrees : ∀ p₀ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₀ p.1) (upper p.1)},
      ∀ p₁ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₁ p.1) (upper p.1)},
        (p₀ : E × ℝ) = (p₁ : E × ℝ) →
        (p₀ : E × ℝ).2 = upper (p₀ : E × ℝ).1 → (C₀ p₀ : F) = C₁ p₁)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite) (hJR : J.space = R)
    {a b : ℝ} (hbound₀ : ∀ x ∈ B, lower₀ x ≤ a)
    (hbound₁ : ∀ x ∈ B, lower₁ x ≤ a) :
    ∃ G : ((T₀ ∪ R) ∩ {y | A y ∈ Icc a b} : Set F) ≃ₜ
        ((T₁ ∪ R) ∩ {y | A y ∈ Icc a b} : Set F), G.IsFinitePL ∧
      (∀ x, A (G x) = A x) ∧
      ∀ x : (R ∩ {y | A y ∈ Icc a b} : Set F),
        (G ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : F) = x := by
  let W : Set (E × ℝ) := {p | p.1 ∈ B ∧ p.2 ∈ Icc a b ∧ p.2 ≤ upper p.1}
  let Rb := R ∩ {y | A y ∈ Icc a b}
  obtain ⟨D₀, D₁, hD₀, hD₁, hD₀height, hD₁height, hD₀val, hD₁val⟩ :=
    hC₀.exists_common_collarBand_restrictions hC₁ A hheight₀ hheight₁ hbound₀ hbound₁
  let i₀ : W → {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₀ p.1) (upper p.1)} :=
    fun p => ⟨p, p.property.1,
      (hbound₀ _ p.property.1).trans p.property.2.1.1, p.property.2.2⟩
  let i₁ : W → {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₁ p.1) (upper p.1)} :=
    fun p => ⟨p, p.property.1,
      (hbound₁ _ p.property.1).trans p.property.2.1.1, p.property.2.2⟩
  have hR₀ (p : W) : (D₀ p : F) ∈ Rb ↔
      (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
    constructor
    · intro hp
      rw [hD₀val] at hp
      exact (hcontact₀ (i₀ p)).mp hp.1
    · intro hp
      refine ⟨?_, (D₀ p).property.2⟩
      rw [hD₀val]
      exact (hcontact₀ (i₀ p)).mpr hp
  have hR₁ (p : W) : (D₁ p : F) ∈ Rb ↔
      (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
    constructor
    · intro hp
      rw [hD₁val] at hp
      exact (hcontact₁ (i₁ p)).mp hp.1
    · intro hp
      refine ⟨?_, (D₁ p).property.2⟩
      rw [hD₁val]
      exact (hcontact₁ (i₁ p)).mpr hp
  have hRagree (p : W) (hp : (p : E × ℝ).2 = upper (p : E × ℝ).1) :
      (D₀ p : F) = D₁ p := by
    rw [hD₀val, hD₁val]
    exact hagrees (i₀ p) (i₁ p) rfl hp
  obtain ⟨Jb, hJb, hJbR⟩ := J.exists_finite_affineSlab_complex hJ A a b
  rw [hJR] at hJbR
  obtain ⟨F, hF, hFA, hFR, _, _, _⟩ :=
    hD₀.exists_height_preserving_union_fixing_residual
      (q := {p : E × ℝ | p.2 = upper p.1}) hD₁ hR₀ hR₁ hRagree Jb hJb hJbR A
      (fun p => (hD₁height p).trans (hD₀height p).symm)
  have hsrc : ((T₀ ∩ {y | A y ∈ Icc a b}) ∪ Rb) =
      (T₀ ∪ R) ∩ {y | A y ∈ Icc a b} := (union_inter_distrib_right _ _ _).symm
  have htgt : ((T₁ ∩ {y | A y ∈ Icc a b}) ∪ Rb) =
      (T₁ ∪ R) ∩ {y | A y ∈ Icc a b} := (union_inter_distrib_right _ _ _).symm
  let G := (Homeomorph.setCongr hsrc.symm).trans (F.trans (Homeomorph.setCongr htgt))
  exact ⟨G, hF.setCongr hsrc htgt,
    fun x => hFA ⟨x, hsrc.symm ▸ x.property⟩, fun x => hFR x⟩

end Homeomorph
