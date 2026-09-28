import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.VerticalAlignment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapAlignment
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift.Reflection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Relative.HalfSpace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

def terminalCylinder {v : E3} (Q : Set (Hemisphere.Plane v)) (a b : Real) : Set E3 :=
  (fun z : Hemisphere.Plane v × Real => z.2 • v + (z.1 : E3)) '' (Q ×ˢ Icc a b)

theorem isCompact_terminalCylinder {v : E3} {Q : Set (Hemisphere.Plane v)}
    (hQ : IsCompact Q) (a b : Real) : IsCompact (terminalCylinder Q a b) :=
  (hQ.prod isCompact_Icc).image (by fun_prop)

theorem isCompact_canonicalNorthernCap (v : E3) :
    IsCompact (boundedCylinderNorthernCap v) := by
  apply IsCompact.image
  · exact (isClosed_le continuous_const (by fun_prop)).isCompact
  · exact (contMDiff_boundedCylinderRadius v).continuous.smul continuous_subtype_val

theorem exists_supported_canonical_lower_cap_vertical_alignment
    {v : E3} (hv : ‖v‖ = 1)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {Q : Set (Hemisphere.Plane v)} (hQ : IsCompact Q)
    {a d b s t : Real} (hab : a < b) (hdb : d < b) (hs : s < 0) (ht : t < 0) :
    ∃ c : Real, max a d < c ∧ c < b ∧
      ∃ S : Set E3, IsCompact S ∧ S ⊆ {y | inner Real v y < c} ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ S, F y = y) ∧
        (∀ y, c ≤ inner Real v y → F y = y) ∧
        F '' (liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
          terminalCylinder Q a b) =
          liftPlaneDiffeomorph hv d t ht.ne A '' boundedCylinderNorthernCap v ∪
            terminalCylinder Q d b := by
  let H := ((ContinuousLinearEquiv.prodComm Real (Hemisphere.Plane v) Real).trans
    (heightCoordinates hv)).toDiffeomorph
  have hHheight (z : Hemisphere.Plane v × Real) : inner Real v (H z) = z.2 :=
    congrArg Prod.snd (H.symm_apply_apply z)
  let L := liftPlaneDiffeomorph hv a s hs.ne A
  let C := H.symm '' (L '' boundedCylinderNorthernCap v)
  have hC : IsCompact C := ((isCompact_canonicalNorthernCap v).image L.continuous).image
    H.symm.continuous
  have hbelow (z : Hemisphere.Plane v × Real) (hz : z ∈ C) : z.2 ≤ a := by
    rcases hz with ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    change inner Real v (L y) ≤ a
    rw [inner_liftPlaneDiffeomorph]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hs.le
      (height_nonneg_of_mem_boundedCylinderNorthernCap hy))
  obtain ⟨c, hmc, hcb, S, hS, hSc, F, hfix, hfixed, _, himage⟩ :=
    exists_supported_vertical_cap_alignment hC hQ hab hdb (div_pos_of_neg_of_neg ht hs)
      hbelow
  let G := (H.symm.trans F).trans H
  have hG (z : Hemisphere.Plane v × Real) : G (H z) = H (F z) := by
    change H (F (H.symm (H z))) = _
    rw [H.symm_apply_apply]
  have hHC : H '' C = L '' boundedCylinderNorthernCap v := by
    rw [image_image]
    simp only [H.apply_symm_apply, image_id']
  have hHQ (a' : Real) : H '' (Q ×ˢ Icc a' b) = terminalCylinder Q a' b := rfl
  have hcap : H '' ((fun z : Hemisphere.Plane v × Real =>
      (z.1, d + (t / s) * (z.2 - a))) '' C) =
        liftPlaneDiffeomorph hv d t ht.ne A '' boundedCylinderNorthernCap v := by
    dsimp [C]
    rw [image_image, image_image, image_image]
    apply image_congr
    intro y _
    change (d + (t / s) * (inner Real v (L y) - a)) • v +
      (((Hemisphere.Plane v).orthogonalProjectionOnto (L y)) : E3) = _
    rw [inner_liftPlaneDiffeomorph, projection_liftPlaneDiffeomorph,
      liftPlaneDiffeomorph_apply]
    congr 2
    field_simp [hs.ne]
    ring
  refine ⟨c, hmc, hcb, H '' S, hS.image H.continuous, ?_, G, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change inner Real v (H z) < c
    rw [hHheight]
    exact hSc hz
  · intro y hy
    have hn : H.symm y ∉ S := fun h => hy ⟨H.symm y, h, H.apply_symm_apply y⟩
    change H (F (H.symm y)) = y
    rw [hfix _ hn, H.apply_symm_apply]
  · intro y hy
    change H (F (H.symm y)) = y
    rw [hfixed _ hy, H.apply_symm_apply]
  · change G '' (L '' boundedCylinderNorthernCap v ∪ terminalCylinder Q a b) = _
    rw [← hHC, ← hHQ a, ← image_union, image_image]
    have heq : (fun z => G (H z)) = fun z => H (F z) := funext hG
    rw [heq, ← image_image, himage, image_union, hcap, hHQ]

theorem exists_complete_lower_cap_alignment
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {d c s : Real} (hdc : d < c) (hs : s < 0) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, c ≤ inner Real v y → D y = y) ∧
      (∀ (t : Real) (p : S1), D (t • v + (γ p : E3)) = t • v + (γ p : E3)) ∧
      D '' (liftPlaneDiffeomorph hv d s hs.ne B '' boundedCylinderNorthernCap v) =
        liftPlaneDiffeomorph hv d s hs.ne A '' boundedCylinderNorthernCap v := by
  obtain ⟨F, hfixed, hcircle, hcap⟩ := exists_complete_upper_cap_alignment
    hv γ hγ A B hA hB (neg_lt_neg hdc) (neg_pos.mpr hs)
  let R := heightReflection hv
  let D := (R.trans F).trans R
  refine ⟨D, ?_, ?_, ?_⟩
  · intro y hy
    change R (F (R y)) = y
    rw [hfixed _ (by simpa only [R, inner_heightReflection] using neg_le_neg hy)]
    exact heightReflection_heightReflection hv y
  · intro t p
    change R (F (R (t • v + (γ p : E3)))) = _
    rw [heightReflection_height_add_plane, hcircle,
      heightReflection_height_add_plane, neg_neg]
  · change (R ∘ F ∘ R) '' _ = _
    rw [image_comp, image_comp, image_heightReflection_liftPlaneDiffeomorph,
      hcap, image_heightReflection_liftPlaneDiffeomorph]
    simp only [neg_neg]

theorem exists_supported_complete_lower_cap_alignment
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {d₁ d₂ b s₁ s₂ : Real} (hd₁ : d₁ < b) (hd₂ : d₂ < b)
    (hs₁ : s₁ < 0) (hs₂ : s₂ < 0) :
    ∃ c : Real, max d₁ d₂ < c ∧ c < b ∧
      ∃ S : Set E3, IsCompact S ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ S, F y = y) ∧
        (∀ y, c ≤ inner Real v y → F y = y) ∧
        F '' (liftPlaneDiffeomorph hv d₁ s₁ hs₁.ne A '' boundedCylinderNorthernCap v ∪
          terminalCylinder (range γ) d₁ b) =
          liftPlaneDiffeomorph hv d₂ s₂ hs₂.ne B '' boundedCylinderNorthernCap v ∪
            terminalCylinder (range γ) d₂ b := by
  have hγcompact : IsCompact (range γ) := isCompact_range hγ.contMDiff.continuous
  obtain ⟨c, hmc, hcb, S₁, hS₁, _, F₁, hfix₁, hfixed₁, himage₁⟩ :=
    exists_supported_canonical_lower_cap_vertical_alignment hv A hγcompact hd₁ hd₂ hs₁ hs₂
  have hd₂c : d₂ < c := (le_max_right _ _).trans_lt hmc
  obtain ⟨D, hDfixed, hDcircle, hDcap⟩ :=
    exists_complete_lower_cap_alignment hv γ hγ B A hB hA hd₂c hs₂
  let K := liftPlaneDiffeomorph hv d₂ s₂ hs₂.ne A '' boundedCylinderNorthernCap v ∪
    terminalCylinder (range γ) d₂ b
  have hK : IsCompact K :=
    ((isCompact_canonicalNorthernCap v).image
      (liftPlaneDiffeomorph hv d₂ s₂ hs₂.ne A).continuous).union
        (isCompact_terminalCylinder hγcompact d₂ b)
  have hDfix : EqOn D id {y | c ≤ inner Real v y} := fun y hy => hDfixed y hy
  obtain ⟨S₂, hS₂, F₂, hfix₂, hfixed₂, hagree⟩ :=
    exists_supported_agreement_of_fixed_halfspace (innerSL Real v) v
      (by simp [hv]) c D hDfix hK
  have hcylinder : D '' terminalCylinder (range γ) d₂ b =
      terminalCylinder (range γ) d₂ b := by
    have heq : EqOn D id (terminalCylinder (range γ) d₂ b) := by
      rintro y ⟨⟨x, t⟩, ⟨⟨p, rfl⟩, ht⟩, rfl⟩
      exact hDcircle t p
    rw [image_congr heq, image_id]
  have himage₂ : F₂ '' K =
      liftPlaneDiffeomorph hv d₂ s₂ hs₂.ne B '' boundedCylinderNorthernCap v ∪
        terminalCylinder (range γ) d₂ b := by
    rw [image_congr hagree]
    change D '' (_ ∪ _) = _
    rw [image_union, hDcap, hcylinder]
  refine ⟨c, hmc, hcb, S₁ ∪ S₂, hS₁.union hS₂, F₁.trans F₂, ?_, ?_, ?_⟩
  · intro y hy
    change F₂ (F₁ y) = y
    rw [hfix₁ y (fun h => hy (Or.inl h)), hfix₂ y (fun h => hy (Or.inr h))]
  · intro y hy
    change F₂ (F₁ y) = y
    rw [hfixed₁ y hy]
    exact hfixed₂ hy
  · change (F₂ ∘ F₁) '' _ = _
    rw [image_comp, himage₁]
    exact himage₂

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
