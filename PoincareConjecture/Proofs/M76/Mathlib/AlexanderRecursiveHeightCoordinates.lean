import PoincareConjecture.Proofs.M76.Mathlib.VariableHeightBand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]








theorem IsFinitePL.exists_moved_collar_height_coordinates_with_endpoints
    {B : Set E} {T R : Set F} {upper : E → ℝ}
    (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : F →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hcontact : ∀ p, (C p : F) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    {g : F → ℝ} (hg : FinitePiecewiseAffineOn g T)
    (hgbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → g (C p) = 0)
    (hgtop : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = upper (p : E × ℝ).1 → g (C p) = 0)
    (v : F) (hv : A.linear v = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ H : F ≃ₜ F,
      FinitePiecewiseAffineOn (H : F → F) T →
      (∀ y ∈ T, H y = y + (ε * g y) • v) →
      ∃ D : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ (H '' T),
        D.IsFinitePL ∧ (∀ p, A (D p) = (p : E × ℝ).2) ∧
        (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
          (p : E × ℝ).2 = 0 ∨ (p : E × ℝ).2 = upper (p : E × ℝ).1 →
            (D p : F) = C p) ∧
        ∀ p, (D p : F) ∈ H '' R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
  let S : Set (E × ℝ) := {p | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)}
  have hcopy := hC
  obtain ⟨f, hf, hval⟩ := hcopy
  have hmap : MapsTo f S T := by
    intro p hp
    rw [← hval ⟨p, hp⟩]
    exact (C ⟨p, hp⟩).property
  have hgf : FinitePiecewiseAffineOn (g ∘ f) S := hg.comp hf hmap
  obtain ⟨δ, hδ, hband⟩ := hgf.exists_variable_heightBand_homeomorph hupper
  refine ⟨δ, hδ, fun ε hε H hH hformula => ?_⟩
  obtain ⟨K, hK, hKval⟩ := hband ε hε
  have hbot (x : E) (hx : x ∈ B) : (g ∘ f) (x, 0) = 0 := by
    change g (f (x, 0)) = 0
    rw [← hval ⟨(x, 0), hx, le_rfl, hupper x hx⟩]
    exact hgbottom _ rfl
  have htop (x : E) (hx : x ∈ B) : (g ∘ f) (x, upper x) = 0 := by
    change g (f (x, upper x)) = 0
    rw [← hval ⟨(x, upper x), hx, hupper x hx, le_rfl⟩]
    exact hgtop _ rfl
  have hbandEq : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈
      Icc (0 + ε * (g ∘ f) (p.1, 0))
        (upper p.1 + ε * (g ∘ f) (p.1, upper p.1))} = S := by
    ext p
    constructor
    · intro hp
      have hp' := hp.2
      rw [hbot p.1 hp.1, htop p.1 hp.1, mul_zero, add_zero, add_zero] at hp'
      exact ⟨hp.1, hp'⟩
    · intro hp
      refine ⟨hp.1, ?_⟩
      rw [hbot p.1 hp.1, htop p.1 hp.1, mul_zero, add_zero, add_zero]
      exact hp.2
  let K' : S ≃ₜ S := (Homeomorph.setCongr (rfl : S = S)).trans
    (K.trans (Homeomorph.setCongr hbandEq))
  have hK' : K'.IsFinitePL := hK.setCongr rfl hbandEq
  have hK'val (p : S) : (K' p : E × ℝ) =
      ((p : E × ℝ).1, (p : E × ℝ).2 + ε * g (C p)) := by
    change (K p : E × ℝ) = _
    rw [hKval, hval p]
    rfl
  have hK'base (p : S) : (K' p : E × ℝ).1 = (p : E × ℝ).1 := by
    simpa only using congrArg (fun w : E × ℝ => w.1) (hK'val p)
  have hK'fix (p : S) (hp : (p : E × ℝ).2 = 0 ∨
      (p : E × ℝ).2 = upper (p : E × ℝ).1) : K' p = p := by
    apply Subtype.ext
    rw [hK'val]
    have hz : g (C p) = 0 := hp.elim (hgbottom p) (hgtop p)
    rw [hz, mul_zero, add_zero]
  have hK'top (p : S) :
      (K' p : E × ℝ).2 = upper (K' p : E × ℝ).1 ↔
        (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
    constructor
    · intro hp
      let z : S := ⟨((p : E × ℝ).1, upper (p : E × ℝ).1),
        p.property.1, hupper _ p.property.1, le_rfl⟩
      have hz : K' z = z := hK'fix z (Or.inr rfl)
      have heq : K' p = K' z := by
        rw [hz]
        apply Subtype.ext
        apply Prod.ext
        · exact hK'base p
        · exact hp.trans (congrArg upper (hK'base p))
      exact congrArg (fun w : S => (w : E × ℝ).2) (K'.injective heq)
    · intro hp
      rw [hK'fix p (Or.inr hp)]
      exact hp
  let D : S ≃ₜ (H '' T) := K'.symm.trans (C.trans (H.image T))
  have hD : D.IsFinitePL := hK'.symm.trans (hC.trans ⟨H, hH, fun _ => rfl⟩)
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · intro p
    let z := K'.symm p
    have hpheight : (p : E × ℝ).2 = (z : E × ℝ).2 + ε * g (C z) := by
      have h := congrArg Prod.snd (hK'val z)
      simpa only [z, K'.apply_symm_apply] using h
    change A (H (C z)) = (p : E × ℝ).2
    rw [hformula (C z) (C z).property, add_comm (C z : F)]
    change A ((ε * g (C z)) • v +ᵥ (C z : F)) = _
    rw [A.map_vadd, map_smul, hv, hheight z, hpheight]
    change (ε * g (C z)) * 1 + (z : E × ℝ).2 =
      (z : E × ℝ).2 + ε * g (C z)
    ring
  · intro p hp
    have hfix : K'.symm p = p := by
      apply K'.injective
      rw [K'.apply_symm_apply, hK'fix p hp]
    change H (C (K'.symm p)) = C p
    rw [hfix, hformula (C p) (C p).property, hp.elim (hgbottom p) (hgtop p),
      mul_zero, zero_smul, add_zero]
  · intro p
    change H (C (K'.symm p)) ∈ H '' R ↔ _
    rw [H.injective.mem_set_image, hcontact]
    have h := hK'top (K'.symm p)
    simpa only [K'.apply_symm_apply] using h.symm




theorem IsFinitePL.exists_moved_collar_height_coordinates
    {B : Set E} {T R : Set F} {upper : E → ℝ}
    (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : F →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hcontact : ∀ p, (C p : F) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    {g : F → ℝ} (hg : FinitePiecewiseAffineOn g T)
    (hgbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → g (C p) = 0)
    (hgtop : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = upper (p : E × ℝ).1 → g (C p) = 0)
    (v : F) (hv : A.linear v = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ H : F ≃ₜ F,
      FinitePiecewiseAffineOn (H : F → F) T →
      (∀ y ∈ T, H y = y + (ε * g y) • v) →
      ∃ D : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ (H '' T),
        D.IsFinitePL ∧ (∀ p, A (D p) = (p : E × ℝ).2) ∧
        (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
          (p : E × ℝ).2 = 0 → (D p : F) = C p) ∧
        ∀ p, (D p : F) ∈ H '' R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
  obtain ⟨δ, hδ, hcoords⟩ := hC.exists_moved_collar_height_coordinates_with_endpoints
    hupper A hheight hcontact hg hgbottom hgtop v hv
  refine ⟨δ, hδ, fun ε hε H hH hformula => ?_⟩
  obtain ⟨D, hD, hheight, hfix, hcontact⟩ := hcoords ε hε H hH hformula
  exact ⟨D, hD, hheight, fun p hp => hfix p (Or.inl hp), hcontact⟩

end Homeomorph
