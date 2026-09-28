import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Rims.SpanningComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalStripEndPaths

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem exists_spanning_complement_paths
    {L Q : Set P2} (c : Bool → P2 → P2)
    (hc : ∀ i, ContinuousOn (c i) source) (sign : Bool → Bool)
    (H : Sq ≃ₜ L)
    (hHQ : ∀ z : Sq, (H z : P2) ∈ Q ↔ (z : P2).2 = 0)
    (hleft : ∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (!(sign false))))
    (hright : ∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (!(sign true)))) :
    let a := c false (0, farArmParameter (sign false))
    let b := c true (0, farArmParameter (sign true))
    let a' := c false (0, farArmParameter (!(sign false)))
    let b' := c true (0, farArmParameter (!(sign true)))
    let V := (L ∩ Q) ∪ (c false '' stripEnd 0 ∪ c true '' stripEnd 0)
    ∃ (D₀ : Path a a') (B : Path a' b') (D₁ : Path b b'),
      (∀ t : I, D₀ t = c false (0, originalStripEndParameter (!(sign false)) t)) ∧
      (∀ t : I, B t = H ⟨(t, 0), t.property, by norm_num⟩) ∧
      (∀ t : I, D₁ t = c true (0, originalStripEndParameter (!(sign true)) t)) ∧
      (∀ t, D₀ t ∈ c false '' stripEnd 0) ∧
      (∀ t, B t ∈ L ∩ Q) ∧ (∀ t, D₁ t ∈ c true '' stripEnd 0) ∧
      ∀ t, (D₀.trans (B.trans D₁.symm)) t ∈ V := by
  let a := c false (0, farArmParameter (sign false))
  let b := c true (0, farArmParameter (sign true))
  let a' := c false (0, farArmParameter (!(sign false)))
  let b' := c true (0, farArmParameter (!(sign true)))
  let D₀ : Path a a' := (originalStripEndPath (c false) (hc false) 0 (!(sign false))).cast
    (by simp [a]) rfl
  let D₁ : Path b b' := (originalStripEndPath (c true) (hc true) 0 (!(sign true))).cast
    (by simp [b]) rfl
  let B : Path a' b' :=
    { toFun t := H ⟨(t, 0), t.property, by norm_num⟩
      continuous_toFun := continuous_subtype_val.comp (H.continuous.comp (by fun_prop))
      source' := hleft 0
      target' := hright 0 }
  have hD₀ (t : I) : D₀ t ∈ c false '' stripEnd 0 :=
    originalStripEndPath_mem (c false) (hc false) 0 (!(sign false)) t
  have hD₁ (t : I) : D₁ t ∈ c true '' stripEnd 0 :=
    originalStripEndPath_mem (c true) (hc true) 0 (!(sign true)) t
  have hB (t : I) : B t ∈ L ∩ Q :=
    ⟨(H ⟨(t, 0), t.property, by norm_num⟩).property, (hHQ _).mpr rfl⟩
  refine ⟨D₀, B, D₁, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, hD₀, hB, hD₁, ?_⟩
  intro t
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact Or.inr (Or.inl (hD₀ _))
  · exact Or.inl (hB _)
  · exact Or.inr (Or.inr (hD₁ _))

end PoincareConjecture.M76.Dehn
