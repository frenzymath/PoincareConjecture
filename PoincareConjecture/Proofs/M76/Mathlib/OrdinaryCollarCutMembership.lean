import PoincareConjecture.Proofs.M76.Mathlib.CollarCutMembership
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections











set_option autoImplicit false

open Set Geometry

namespace Homeomorph





theorem collar_complement_map_mem_cut_iff
    {E : Type*} [TopologicalSpace E]
    {B T b w R s₀ s₁ Y : Set E} {upper A : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hcover : T ⊆ s₀ ∪ s₁)
    (hinter : s₀ ∩ s₁ ⊆ b) (hbzero : b ⊆ {x | A x = 0})
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x) (hwb : Disjoint w b)
    (f₀ f₁ : E → E)
    (h₀ : ∀ x ∈ w,
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = x ∧ f₀ x = (C p : E))
    (h₁ : ∀ x ∈ w,
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = x ∧ f₁ x = H (C p))
    (F : ((f₀ '' w) ∪ R : Set E) ≃ₜ Y)
    (hFR : ∀ x : R, (F ⟨x, Or.inr x.property⟩ : E) = x)
    (hFw : ∀ x : w, (F ⟨f₀ x, Or.inl ⟨x, x.property, rfl⟩⟩ : E) = f₁ x) :
    ∀ y : ((f₀ '' w) ∪ R : Set E), (y : E) ∈ s₀ ↔ (F y : E) ∈ H '' s₀ := by
  intro y
  rcases y.property with hyw | hyR
  · obtain ⟨x, hx, hxy⟩ := hyw
    let z : ((f₀ '' w) ∪ R : Set E) := ⟨f₀ x, Or.inl ⟨x, hx, rfl⟩⟩
    have hzy : z = y := Subtype.ext hxy
    rw [← hzy, hFw ⟨x, hx⟩]
    obtain ⟨p₀, hp₀, hf₀⟩ := h₀ x hx
    obtain ⟨p₁, hp₁, hf₁⟩ := h₁ x hx
    have hnot₀ : (p₀ : E × ℝ).1 ∉ b :=
      fun h => disjoint_left.mp hwb hx (hp₀ ▸ h)
    have hnot₁ : (p₁ : E × ℝ).1 ∉ b :=
      fun h => disjoint_left.mp hwb hx (hp₁ ▸ h)
    change f₀ x ∈ s₀ ↔ f₁ x ∈ H '' s₀
    rw [hf₀, hf₁, H.injective.mem_set_image]
    exact ((C.collar_fiber_mem_cut_iff hheight hbottom hs₀ hs₁ hcover
      hinter hbzero p₀ hnot₀).1.trans (by rw [hp₀])).trans
      ((C.collar_fiber_mem_cut_iff hheight hbottom hs₀ hs₁ hcover
        hinter hbzero p₁ hnot₁).1.trans (by rw [hp₁])).symm
  · have hFy : (F y : E) = y := hFR ⟨y, hyR⟩
    rw [hFy, ← hfix y hyR, H.injective.mem_set_image, hfix y hyR]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePL.exists_cut_image_restriction
    {X Y s : Set E} {F : X ≃ₜ Y} (hF : F.IsFinitePL) (H : E ≃ₜ E)
    (hmem : ∀ x : X, (x : E) ∈ s ↔ (F x : E) ∈ H '' s)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKs : K.space = s) :
    ∃ G : (X ∩ s : Set E) ≃ₜ (Y ∩ (H '' s) : Set E), G.IsFinitePL ∧
      ∀ x : (X ∩ s : Set E), (G x : E) = F ⟨x, x.property.1⟩ := by
  have htest (x : X) : (x : E) ∈ X ∩ s ↔ (F x : E) ∈ Y ∩ (H '' s) :=
    ⟨fun hx => ⟨(F x).property, (hmem x).mp hx.2⟩,
      fun hx => ⟨x.property, (hmem x).mpr hx.2⟩⟩
  have hcopy := hF
  obtain ⟨_, ⟨J, hJ, hJX, _⟩, _⟩ := hcopy
  obtain ⟨W, hW, hWs⟩ := J.exists_finite_triangulation_inter K hJ hK
  have hWX : W.space = X ∩ s := by rw [hWs, hJX, hKs]
  let G := F.restrictSubsets inter_subset_left inter_subset_left htest
  exact ⟨G, hF.restrictSubsets inter_subset_left inter_subset_left htest W hW hWX,
    fun _ => rfl⟩

end Homeomorph
