import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Terminal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_lower_cap_height (data : TerminalSaddleData M P p e)
    (j : data.ends.LowerCutIndex) {q : S2}
    (hq : q ∈ terminalEndCap data.ends (.inl j)) :
    inner Real (M.v : E3) (g q) ≤ data.ends.lowerCut := by
  let A := data.ends.lower j.1.1 j.1.2 j.2
  apply A.height_le_cut_of_mem_cappedRegion j.2.le le_rfl
  change q ∈ A.region ∪ _ at hq
  exact hq.elim Or.inr Or.inl

theorem terminal_upper_cap_height (data : TerminalSaddleData M P p e)
    (j : data.ends.UpperCutIndex) {q : S2}
    (hq : q ∈ terminalEndCap data.ends (.inr j)) :
    data.ends.upperCut ≤ inner Real (M.v : E3) (g q) := by
  let A := data.ends.upper j.1.1 j.1.2 j.2
  have hcap : q ∈ A.cappedRegion data.ends.upperCut := by
    change q ∈ A.region ∪ _ at hq
    rw [A.region_eq_image] at hq
    exact hq.elim Or.inr Or.inl
  rw [A.cappedRegion_eq_reflected] at hcap
  have hh := A.reflected.height_le_cut_of_mem_cappedRegion
    (neg_le_neg j.2.le) le_rfl hcap
  simpa only [Poincare.Geometry.Euclidean.inner_heightReflection, neg_le_neg_iff] using hh

theorem lower_halfspace_image_of_fixed_upper
    (R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (v : E3) (b : Real)
    (hR : EqOn R id {y | b ≤ inner Real v y}) {y : E3}
    (hy : inner Real v y ≤ b) : inner Real v (R y) ≤ b := by
  by_contra h
  have hfix := hR (show R y ∈ {z | b ≤ inner Real v z} from (lt_of_not_ge h).le)
  have heq : R y = y := R.injective hfix
  rw [heq] at h
  exact h hy

theorem exists_simultaneous_terminal_replacement_of_side_replacements
    (data : TerminalSaddleData M P p e)
    (E Rlower Rupper : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    {Klower Kupper : Set E3} (hKl : IsCompact Klower) (hKu : IsCompact Kupper)
    (hRl : ∀ y ∉ Klower, Rlower y = y)
    (hRu : ∀ y ∉ Kupper, Rupper y = y)
    {c : Real} (hlc : data.ends.lowerCut ≤ c) (hcu : c ≤ data.ends.upperCut)
    (hRlower : EqOn Rlower id {y | c ≤ inner Real (M.v : E3) y})
    (hRupper : EqOn Rupper id {y | inner Real (M.v : E3) y ≤ c})
    (hRlowerBand : EqOn Rlower id (data.toTerminalSaddleGeometry.flatten ⁻¹'
      data.toTerminalSaddleGeometry.modelBand))
    (hRupperBand : EqOn Rupper id (data.toTerminalSaddleGeometry.flatten ⁻¹'
      data.toTerminalSaddleGeometry.modelBand))
    (hlower : ∀ j : data.ends.LowerCutIndex,
      Rlower '' ((E ∘ g) '' terminalEndCap data.ends (.inl j)) =
        data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelCaps (data.labels.symm (.inl j)))
    (hupper : ∀ j : data.ends.UpperCutIndex,
      Rupper '' ((E ∘ g) '' terminalEndCap data.ends (.inr j)) =
        data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelCaps (data.labels.symm (.inr j))) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧
        EqOn R id (data.toTerminalSaddleGeometry.flatten ⁻¹'
          data.toTerminalSaddleGeometry.modelBand) ∧
        ∀ i, R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i := by
  refine ⟨Klower ∪ Kupper, hKl.union hKu, Rlower.trans Rupper, ?_, ?_, ?_⟩
  · intro y hy
    change Rupper (Rlower y) = y
    rw [hRl y (fun h => hy (Or.inl h)), hRu y (fun h => hy (Or.inr h))]
  · intro y hy
    change Rupper (Rlower y) = y
    rw [hRlowerBand hy, id_eq, hRupperBand hy, id_eq]
  · intro i
    change (Rupper ∘ Rlower) '' _ = _
    rw [image_comp]
    cases hlabel : data.labels i with
    | inl j =>
      have hi : data.labels.symm (.inl j) = i := by rw [← hlabel, data.labels.symm_apply_apply]
      rw [hlower, hi]
      conv_rhs => rw [← image_id (data.toTerminalSaddleGeometry.flatten.symm ''
        data.toTerminalSaddleGeometry.modelCaps i)]
      apply image_congr
      intro y hy
      rw [← hi, ← hlower j] at hy
      obtain ⟨x, ⟨q, hq, rfl⟩, rfl⟩ := hy
      apply hRupper
      apply lower_halfspace_image_of_fixed_upper Rlower _ _ hRlower
      have hh : inner Real (M.v : E3) ((E ∘ g) q) ≤ data.ends.lowerCut := by
        simpa only [comp_apply, hEheight] using terminal_lower_cap_height data j hq
      exact hh.trans hlc
    | inr j =>
      have hi : data.labels.symm (.inr j) = i := by rw [← hlabel, data.labels.symm_apply_apply]
      have hfixed : Rlower '' ((E ∘ g) '' terminalEndCap data.ends (.inr j)) =
          (E ∘ g) '' terminalEndCap data.ends (.inr j) := by
        conv_rhs => rw [← image_id ((E ∘ g) '' terminalEndCap data.ends (.inr j))]
        apply image_congr
        rintro y ⟨q, hq, rfl⟩
        apply hRlower
        exact hcu.trans (by
          simpa only [comp_apply, hEheight] using terminal_upper_cap_height data j hq)
      rw [hfixed, hupper, hi]

theorem exists_simultaneous_flat_terminal_replacement_of_prepared
    (data : TerminalSaddleData M P p e)
    (H E F R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {K L : Set E3} (hK : IsCompact K) (hL : IsCompact L)
    (hFfix : ∀ y ∉ K, F y = y)
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFcap : ∀ i, F '' (H '' data.toTerminalSaddleGeometry.C i) =
      (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
        terminalEndCap data.ends (data.labels i))
    (hRfix : ∀ y ∉ L, R y = y)
    (hRband : EqOn R id (data.toTerminalSaddleGeometry.flatten ⁻¹'
      data.toTerminalSaddleGeometry.modelBand))
    (hRcap : ∀ i, R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
      data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelCaps i) :
    ∃ S : Set E3, IsCompact S ∧
      ∃ H₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ S, H₂ y = y) ∧ EqOn H₂ id data.toTerminalSaddleGeometry.modelBand ∧
        ∀ i, H₂ '' (H '' data.toTerminalSaddleGeometry.C i) =
          data.toTerminalSaddleGeometry.modelCaps i := by
  let d := data.toTerminalSaddleGeometry
  let H₂ := F.trans (d.flatten.symm.trans (R.trans d.flatten))
  have hH₂ (y : E3) : H₂ y = d.flatten (R (d.flatten.symm (F y))) := rfl
  refine ⟨K ∪ d.flatten '' L, hK.union (hL.image d.flatten.continuous), H₂, ?_, ?_, ?_⟩
  · intro y hy
    rw [hH₂, hFfix y (fun hh => hy (Or.inl hh))]
    have hnot : d.flatten.symm y ∉ L := fun hh =>
      hy (Or.inr ⟨d.flatten.symm y, hh, d.flatten.apply_symm_apply y⟩)
    rw [hRfix _ hnot, d.flatten.apply_symm_apply]
  · intro y hy
    rw [hH₂, hFband hy, id_eq]
    have hh : d.flatten.symm y ∈ d.flatten ⁻¹' d.modelBand := by
      change d.flatten (d.flatten.symm y) ∈ d.modelBand
      rwa [d.flatten.apply_symm_apply]
    rw [hRband hh, id_eq, d.flatten.apply_symm_apply]
  · intro i
    change (d.flatten ∘ R ∘ d.flatten.symm ∘ F) '' (H '' d.C i) = d.modelCaps i
    rw [image_comp, image_comp, image_comp, hFcap]
    have hcancel : d.flatten.symm '' ((d.flatten ∘ E ∘ g) ''
        terminalEndCap data.ends (data.labels i)) =
        (E ∘ g) '' terminalEndCap data.ends (data.labels i) := by
      rw [image_image]
      exact image_congr (fun q _ => d.flatten.symm_apply_apply (E (g q)))
    rw [hcancel, hRcap, image_image]
    change (fun y => d.flatten (d.flatten.symm y)) '' d.modelCaps i = d.modelCaps i
    simp only [Diffeomorph.apply_symm_apply, image_id']

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
