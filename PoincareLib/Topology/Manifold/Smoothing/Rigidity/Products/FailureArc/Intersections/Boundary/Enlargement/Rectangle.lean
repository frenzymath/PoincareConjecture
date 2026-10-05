import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLProperArcExtension
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.PolygonalStripDiskAttachment

/-! # Rectangular coordinates on the whole disk around a returning arc -/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76.Dehn.Annuli

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_proper_arc_rectangle_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T Q W : Set E} {a b : E}
    (hT : IsFinitePLBallPair P2 T Q) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a ∈ Q) (hb : b ∈ Q)
    (hproper : W \ {a, b} ⊆ T \ Q) :
    ∃ (H : source ≃ₜ T) (w : I ≃ₜ W), H.IsFinitePL ∧ w.IsFinitePL ∧
      (w 0 : E) = a ∧ (w 1 : E) = b ∧
      (∀ t : I, (H ⟨((t : ℝ), 0), ⟨t.property, by norm_num⟩⟩ : E) = w t) ∧
      (∀ x : source, (H x : E) ∈ W ↔ (x : P2).2 = 0) ∧
      ∀ x : source, (H x : E) ∈ Q ↔ (x : P2) ∈ stripRim := by
  have hsource : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨haxis, p, hp, hpval⟩ := exists_arm_parameter 0
  obtain ⟨w, hw, hw0, hw1⟩ := hW.exists_unitInterval_chart_with_endpoints hab
  have h01 : ((0, 0) : P2) ≠ (1, 0) := by norm_num
  have h0rim : ((0, 0) : P2) ∈ stripRim := by norm_num [stripRim]
  have h1rim : ((1, 0) : P2) ∈ stripRim := by norm_num [stripRim]
  have haxisProper : arm 0 \ {((0, 0) : P2), (1, 0)} ⊆ source \ stripRim := by
    rintro x ⟨⟨hx, hx0⟩, hends⟩
    have hx0' : x.2 = 0 := hx0
    refine ⟨⟨hx, by rw [hx0']; norm_num⟩, ?_⟩
    rintro (⟨(hzero | hone), _⟩ | ⟨_, hy⟩)
    · exact hends (Or.inl (Prod.ext hzero hx0'))
    · exact hends (Or.inr (Prod.ext hone hx0'))
    · simp only [mem_insert_iff, mem_singleton_iff] at hy
      rcases hy with hy | hy <;> linarith
  let e : arm 0 ≃ₜ W := p.symm.trans w
  have he : e.IsFinitePL := hp.symm.trans hw
  have hends (x : arm 0) : (x : P2) ∈ ({(0, 0), (1, 0)} : Set P2) ↔
      (e x : E) ∈ ({a, b} : Set E) := by
    obtain ⟨t, rfl⟩ := p.surjective x
    simp only [e, Homeomorph.trans_apply, p.symm_apply_apply, mem_insert_iff,
      mem_singleton_iff, ← hw0, ← hw1, Subtype.coe_inj, w.injective.eq_iff, hpval,
      Prod.mk.injEq, and_true]
    exact or_congr ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
      ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  obtain ⟨H, hH, hHe, hHW, hHQ⟩ := hsource.exists_extension_of_proper_arc hT haxis hW
    h01 hab h0rim h1rim ha hb haxisProper hproper e he hends
  refine ⟨H, w, hH, hw, hw0, hw1, ?_, ?_, fun x ↦ (hHQ x).symm⟩
  · intro t
    have ht : ((t : ℝ), (0 : ℝ)) ∈ source := ⟨t.property, by norm_num⟩
    have hpoint : (⟨((t : ℝ), 0), ⟨t.property, rfl⟩⟩ : arm 0) = p t :=
      Subtype.ext (hpval t).symm
    have hh := hHe ⟨((t : ℝ), 0), ⟨t.property, rfl⟩⟩ ht
    exact hh.trans ((congrArg (fun z : arm 0 ↦ (e z : E)) hpoint).trans (by
      simp only [e, Homeomorph.trans_apply, p.symm_apply_apply]))
  · intro x
    have hmem : (x : P2) ∈ arm 0 ↔ (x : P2).2 = 0 := by
      simp only [arm, mem_prod, mem_singleton_iff, x.property.1, true_and]
    exact (hHW x).symm.trans hmem

end PoincareMT.M76.Dehn.Annuli
