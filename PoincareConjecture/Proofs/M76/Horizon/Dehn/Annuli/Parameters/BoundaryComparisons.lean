import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.HomotopicRimExtension

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1
local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_annulus_boundary_comparisons
    {E : Type*} [TopologicalSpace E] [T2Space E] {T : Set E}
    (c : Ann ≃ₜ T) (B : Bool → Set E) (hB : ∀ b, B b ⊆ T)
    (gamma : ∀ b, Circle ≃ₜ B b)
    (hrim : ∀ (b : Bool) (x : Ann),
      depth 8 (x : P2) = (if b then 1 else -1) ↔ (c x : E) ∈ B b) :
    ∃ q : Bool → Circle ≃ₜ Circle, ∀ (b : Bool) (z : Circle),
      (c (annulusRimPoint b (q b z)) : E) = (gamma b z : E) := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have hF (b : Bool) : ∃ F : Circle ≃ₜ B b,
      ∀ z, (F z : E) = (c (annulusRimPoint b z) : E) := by
    let f : Circle → B b := fun z ↦ ⟨c (annulusRimPoint b z),
      (hrim b _).mp (depth_annulusRimPoint b z)⟩
    have hf : Continuous f :=
      (continuous_subtype_val.comp (c.continuous.comp (continuous_annulusRimPoint b))).subtype_mk _
    have hfi : Function.Injective f := by
      intro z w h
      have hh : (c (annulusRimPoint b z) : E) = (c (annulusRimPoint b w) : E) :=
        congrArg (fun y : B b ↦ (y : E)) h
      exact injective_annulusRimPoint b (c.injective (Subtype.ext hh))
    have hfs : Function.Surjective f := by
      intro y
      let x : Ann := c.symm ⟨y, hB b y.property⟩
      have hx : depth 8 (x : P2) = if b then 1 else -1 := (hrim b x).mpr (by
        change (c (c.symm ⟨y, hB b y.property⟩) : E) ∈ B b
        simpa only [c.apply_symm_apply] using y.property)
      obtain ⟨z, hz⟩ := (range_annulusRimPoint b).symm.subset hx
      refine ⟨z, Subtype.ext ?_⟩
      change (c (annulusRimPoint b z) : E) = (y : E)
      rw [hz]
      exact congrArg Subtype.val (c.apply_symm_apply ⟨y, hB b y.property⟩)
    let F : Circle ≃ₜ B b := Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective f ⟨hfi, hfs⟩) hf
    exact ⟨F, fun _ ↦ rfl⟩
  choose F hFv using hF
  refine ⟨fun b ↦ (gamma b).trans (F b).symm, ?_⟩
  intro b z
  exact (hFv b _).symm.trans (congrArg Subtype.val ((F b).apply_symm_apply (gamma b z)))

theorem exists_finitePL_annulus_boundary_comparisons
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (B : Bool → Set E) (hB : ∀ b, B b ⊆ T) (gamma : ∀ b, Circle ≃ₜ B b)
    (hgamma : ∀ b, FinitePiecewiseAffineOn
      (fun s : ℝ ↦ (gamma b ((32 * s : ℝ) : Circle) : E)) I)
    (hrim : ∀ (b : Bool) (x : Ann),
      depth 8 (x : P2) = (if b then 1 else -1) ↔ (c x : E) ∈ B b) :
    ∃ q : Bool → Circle ≃ₜ Circle,
      (∀ (b : Bool) (z : Circle),
        (c (annulusRimPoint b (q b z)) : E) = (gamma b z : E)) ∧
      ∀ b, FinitePiecewiseAffineOn (fun s : ℝ ↦ annulusMap 8 (by norm_num)
        (q b ((32 * s : ℝ) : Circle), if b then 1 else -1)) I := by
  obtain ⟨q, hq⟩ := exists_annulus_boundary_comparisons c B hB gamma hrim
  obtain ⟨g, hg, hgv⟩ := hc.symm
  refine ⟨q, hq, ?_⟩
  intro b
  apply (hg.comp (hgamma b) (fun s _ ↦ hB b (gamma b _).property)).congr
  intro s _
  change g (gamma b ((32 * s : ℝ) : Circle)) = _
  rw [← hq b ((32 * s : ℝ) : Circle), ← hgv, c.symm_apply_apply]
  rfl

end PoincareConjecture.M76.Dehn
