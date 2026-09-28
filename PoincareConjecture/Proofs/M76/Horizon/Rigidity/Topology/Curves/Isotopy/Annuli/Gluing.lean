import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.ComplementMatching
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem annular_chart_rim_iff_of_value {T C : Set P2}
    (c : Ann ≃ₜ T) (b : Bool) (gamma : Circle ≃ₜ C)
    (hval : ∀ z, (c (annulusRimPoint b z) : P2) = gamma z) (x : Ann) :
    (c x : P2) ∈ C ↔ depth 8 (x : P2) = (if b then 1 else -1) := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := gamma.surjective ⟨c x, hx⟩
    have hcx : c (annulusRimPoint b z) = c x :=
      Subtype.ext ((hval z).trans (congrArg Subtype.val hz))
    rw [← c.injective hcx]
    exact depth_annulusRimPoint b z
  · intro hx
    obtain ⟨z, rfl⟩ := (range_annulusRimPoint b).symm.subset hx
    rw [hval]
    exact (gamma z).property

theorem exists_annular_gluing_fixing_rims {T₀ T₁ C : Set P2}
    (O : Ann ≃ₜ T₀) (J : Ann ≃ₜ T₁) (gamma : Circle ≃ₜ C)
    (hO : O.IsFinitePL) (hJ : J.IsFinitePL)
    (hcover : T₀ ∪ T₁ = Ann) (hinter : T₀ ∩ T₁ = C)
    (hOzero : ∀ z : Circle, (O (annulusRimPoint false z) : P2) = annulusRimPoint false z)
    (hOone : ∀ z : Circle, (O (annulusRimPoint true z) : P2) = gamma z)
    (hJzero : ∀ z : Circle, (J (annulusRimPoint false z) : P2) = gamma z)
    (hJone : ∀ z : Circle, (J (annulusRimPoint true z) : P2) = annulusRimPoint true z) :
    ∃ G : Ann ≃ₜ Ann, G.IsFinitePL ∧
      (∀ b z, G (annulusRimPoint b z) = annulusRimPoint b z) ∧
      ∀ z : Circle, (G (annulusCoreCircle z) : P2) = gamma z := by
  obtain ⟨S₀, hS₀, hd₀, hS₀zero, hS₀one⟩ := exists_finitePL_annularDepthHalf_rims false
  obtain ⟨S₁, hS₁, hd₁, hS₁zero, hS₁one⟩ := exists_finitePL_annularDepthHalf_rims true
  simp only [Bool.false_eq_true, ↓reduceIte] at hd₀ hS₀zero hS₀one hd₁ hS₁zero hS₁one
  let e₀ := S₀.symm.trans O
  let e₁ := S₁.symm.trans J
  have hover (x : annularDepthHalf false) :
      (x : P2) ∈ annularDepthHalf true ↔ (e₀ x : P2) ∈ T₁ := by
    have hdepth := hd₀ (S₀.symm x)
    rw [S₀.apply_symm_apply] at hdepth
    have ht : (e₀ x : P2) ∈ T₁ ↔ (O (S₀.symm x) : P2) ∈ C := by
      change (O (S₀.symm x) : P2) ∈ T₁ ↔ _
      rw [← hinter]
      exact (and_iff_right (O _).property).symm
    rw [ht, annular_chart_rim_iff_of_value O true gamma hOone]
    change ((x : P2) ∈ Ann ∧ 0 ≤ depth 8 (x : P2)) ↔
      depth 8 (S₀.symm x : P2) = 1
    have hx := x.property.2
    change depth 8 (x : P2) ≤ 0 at hx
    constructor
    · intro h
      linarith [h.2]
    · intro h
      exact ⟨x.property.1, by linarith⟩
  have hagree (x : P2) (hx₀ : x ∈ annularDepthHalf false)
      (hx₁ : x ∈ annularDepthHalf true) :
      (e₀ ⟨x, hx₀⟩ : P2) = e₁ ⟨x, hx₁⟩ := by
    have hz : depth 8 x = 0 := le_antisymm hx₀.2 hx₁.2
    have hd0 := hd₀ (S₀.symm ⟨x, hx₀⟩)
    have hd1 := hd₁ (S₁.symm ⟨x, hx₁⟩)
    rw [S₀.apply_symm_apply, hz] at hd0
    rw [S₁.apply_symm_apply, hz] at hd1
    have h0 : depth 8 (S₀.symm ⟨x, hx₀⟩ : P2) = 1 := by linarith
    have h1 : depth 8 (S₁.symm ⟨x, hx₁⟩ : P2) = -1 := by linarith
    obtain ⟨z, hz⟩ := (range_annulusRimPoint true).symm.subset h0
    obtain ⟨w, hw⟩ := (range_annulusRimPoint false).symm.subset h1
    have hzw : z = w := by
      have hc : annulusCoreCircle z = annulusCoreCircle w := by
        apply Subtype.ext
        rw [← hS₀one, ← hS₁zero, hz, hw, S₀.apply_symm_apply, S₁.apply_symm_apply]
      exact congrArg Prod.snd (annulusCylinderHomeomorph.injective hc)
    change (O (S₀.symm ⟨x, hx₀⟩) : P2) = J (S₁.symm ⟨x, hx₁⟩)
    rw [← hz, ← hw, hOone, hJzero, hzw]
  obtain ⟨G, hG, hG₀, hG₁⟩ := Homeomorph.exists_union_finitePL e₀ e₁
    (hS₀.symm.trans hO) (hS₁.symm.trans hJ) hover hagree
  let G' := (Homeomorph.setCongr annularDepthHalf_union.symm).trans
    (G.trans (Homeomorph.setCongr hcover))
  have hG' : G'.IsFinitePL := hG.setCongr annularDepthHalf_union hcover
  have hleft (z : Ann) : (G' ⟨S₀ z, annularDepthHalf_union.subset (Or.inl (S₀ z).property)⟩ : P2) = O z := by
    change (G ⟨S₀ z, _⟩ : P2) = _
    rw [hG₀]
    change (O (S₀.symm (S₀ z)) : P2) = O z
    rw [S₀.symm_apply_apply]
  have hright (z : Ann) : (G' ⟨S₁ z, annularDepthHalf_union.subset (Or.inr (S₁ z).property)⟩ : P2) = J z := by
    change (G ⟨S₁ z, _⟩ : P2) = _
    rw [hG₁]
    change (J (S₁.symm (S₁ z)) : P2) = J z
    rw [S₁.symm_apply_apply]
  refine ⟨G', hG', ?_, ?_⟩
  · intro b z
    apply Subtype.ext
    cases b
    · have h := hleft (annulusRimPoint false z)
      have heq : (⟨S₀ (annulusRimPoint false z), (S₀ _).property.1⟩ : Ann) = annulusRimPoint false z :=
        Subtype.ext (hS₀zero z)
      rw [heq] at h
      exact h.trans (hOzero z)
    · have h := hright (annulusRimPoint true z)
      have heq : (⟨S₁ (annulusRimPoint true z), (S₁ _).property.1⟩ : Ann) = annulusRimPoint true z :=
        Subtype.ext (hS₁one z)
      rw [heq] at h
      exact h.trans (hJone z)
  · intro z
    have h := hleft (annulusRimPoint true z)
    have heq : (⟨S₀ (annulusRimPoint true z), (S₀ _).property.1⟩ : Ann) = annulusCoreCircle z :=
      Subtype.ext (hS₀one z)
    rw [heq] at h
    exact h.trans (hOone z)

end PoincareConjecture.M76.Dehn
