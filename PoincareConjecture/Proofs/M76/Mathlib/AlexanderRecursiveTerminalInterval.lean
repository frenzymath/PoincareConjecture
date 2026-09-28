import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveMovedBand
import PoincareConjecture.Proofs.M76.Mathlib.TerminalCollarBandComparison










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem IsFinitePL.exists_moved_collar_terminal_interval
    {B : Set E} {T R : Set F} {upper bottom : E → ℝ}
    (hupper : ∀ x ∈ B, 0 ≤ upper x) (hbound : ∀ x ∈ B, bottom x ≤ 1)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : F →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hcontact : ∀ p, (C p : F) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    {g : F → ℝ} (hg : FinitePiecewiseAffineOn g T)
    (hgbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → g (C p) = bottom (p : E × ℝ).1)
    (hgR : ∀ x ∈ R, g x = 0)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite) (hJR : J.space = R)
    (v : F) (hv : A.linear v = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → |t| < δ → ∀ H : F ≃ₜ F,
      FinitePiecewiseAffineOn (H : F → F) T →
      (∀ x, H x = x + (t * g x) • v) → ∀ a b : ℝ, t < a →
      ∃ G : ((T ∪ R) ∩ {y | A y ∈ Icc a b} : Set F) ≃ₜ
          (((H '' T) ∪ R) ∩ {y | A y ∈ Icc a b} : Set F), G.IsFinitePL ∧
        (∀ x, A (G x) = A x) ∧
        ∀ x : (R ∩ {y | A y ∈ Icc a b} : Set F),
          (G ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : F) = x := by
  have hgtop (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
      (hp : (p : E × ℝ).2 = upper (p : E × ℝ).1) : g (C p) = 0 :=
    hgR _ ((hcontact p).mpr hp)
  obtain ⟨δ, hδ, hcoords⟩ := hC.exists_moved_collar_height_coordinates_with_bottom_scalar
    hupper A hheight hg hgbottom hgtop v hv
  refine ⟨δ, hδ, fun t ht htδ H hH hformula a b hta => ?_⟩
  obtain ⟨D, hD, hDA, hDroof, hDbase⟩ :=
    hcoords t htδ H hH (fun x _ => hformula x)
  have hfix (x : F) (hx : x ∈ R) : H x = x := by
    rw [hformula, hgR x hx, mul_zero, zero_smul, add_zero]
  have hmem (x : F) : H x ∈ R ↔ x ∈ R := by
    constructor
    · intro hx
      have heq : H x = x := H.injective (hfix _ hx)
      exact heq ▸ hx
    · intro hx
      rwa [hfix x hx]
  have hDcontact (p : {p : E × ℝ | p.1 ∈ B ∧
      p.2 ∈ Icc (t * bottom p.1) (upper p.1)}) :
      (D p : F) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
    obtain ⟨z, _, hval, hroof⟩ := hDbase p
    rw [hval, hmem, hcontact]
    exact hroof.symm
  have hagree
      (p₀ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
      (p₁ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (t * bottom p.1) (upper p.1)})
      (hp : (p₀ : E × ℝ) = (p₁ : E × ℝ))
      (hroof : (p₀ : E × ℝ).2 = upper (p₀ : E × ℝ).1) :
      (C p₀ : F) = D p₁ := by
    have hroof₁ : (p₁ : E × ℝ).2 = upper (p₁ : E × ℝ).1 := hp ▸ hroof
    rw [hDroof p₁ hroof₁]
    apply congrArg (fun z => (C z : F))
    apply Subtype.ext
    have hbase : (p₀ : E × ℝ).1 = (p₁ : E × ℝ).1 :=
      congrArg (fun z : E × ℝ => z.1) hp
    exact Prod.ext hbase (hroof.trans (congrArg upper hbase))
  have hlo₀ (x : E) (_hx : x ∈ B) : (0 : ℝ) ≤ a := (ht.trans hta).le
  have hlo₁ (x : E) (hx : x ∈ B) : t * bottom x ≤ a := by
    calc
      t * bottom x ≤ t * 1 := mul_le_mul_of_nonneg_left (hbound x hx) ht.le
      _ = t := mul_one t
      _ ≤ a := hta.le
  exact hC.exists_terminal_collarBand_comparison
    (lower₀ := fun _ => 0) (lower₁ := fun x => t * bottom x)
    hD A hheight hDA hcontact hDcontact hagree J hJ hJR hlo₀ hlo₁

end Homeomorph
