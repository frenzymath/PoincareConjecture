import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.RelativeProjection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.RelativeCentered
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Suspension








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P2 := Real × E2
local notation "IR2" => 𝓘(Real, Real × Real)





theorem exists_relative_matching_of_physical_height_strips
    {g₀ g₁ : S2 → E3}
    (hg₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g₀)
    (hg₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g₁)
    {v : E3} (hv : ‖v‖ = 1) (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2)
    (F₀ F₁ : OpenPartialHomeomorph (Real × Real) S2)
    {l l₀ l₁ u₁ u₀ u w c r R : Real}
    (hr : 0 < r) (hrw : r < w) (hrR : r < R)
    (hll₀ : l ≤ l₀) (hl₀l₁ : l₀ < l₁) (hl₁u₁ : l₁ ≤ u₁)
    (hu₁u₀ : u₁ < u₀) (hu₀u : u₀ ≤ u)
    (hs₀ : F₀.source = Ioo (l - w) (u + w) ×ˢ Ioo (-w) w)
    (hs₁ : F₁.source = Ioo (l - w) (u + w) ×ˢ Ioo (-w) w)
    (hF₀ : ContMDiffOn IR2 (𝓡 2) ∞ F₀ F₀.source)
    (hFi₀ : ContMDiffOn (𝓡 2) IR2 ∞ F₀.symm F₀.target)
    (hF₁ : ContMDiffOn IR2 (𝓡 2) ∞ F₁ F₁.source)
    (hFi₁ : ContMDiffOn (𝓡 2) IR2 ∞ F₁.symm F₁.target)
    (hh₀ : ∀ z ∈ F₀.source, inner Real v (g₀ (F₀ z)) = c + z.2)
    (hh₁ : ∀ z ∈ F₁.source, inner Real v (g₁ (F₁ z)) = c + z.2)
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hcentral : ∀ s ∈ Icc l u,
      Q (stripPlaneMap g₀ v J F₀ (s, 0)) = stripPlaneMap g₁ v J F₁ (s, 0))
    (hends : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u,
      Q (stripPlaneMap g₀ v J F₀ (s, t)) = stripPlaneMap g₁ v J F₁ (s, t))
    {U : Set E2} (hU : IsOpen U)
    (hproject₀ : ∀ q ∈ F₀.target, Q (J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g₀ q))) ∈ U)
    (hproject₁ : ∀ q ∈ F₁.target, J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g₁ q)) ∈ U) :
    ∃ (K : Set E2) (V : Set P2), IsCompact K ∧ K ⊆ U ∧ IsOpen V ∧
      (∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l l₀ ∪ Icc u₀ u,
        (t, stripPlaneMap g₀ v J F₀ (s, t)) ∈ V) ∧
      ∃ H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
        (∀ z, (H z).1 = z.1) ∧
        (∀ x, H (0, x) = (0, Q x)) ∧
        (∀ z, (z.1, Q z.2) ∉ closedBall (0 : Real) R ×ˢ K → H z = (z.1, Q z.2)) ∧
        (∀ z ∈ V, H z = (z.1, Q z.2)) ∧
        (∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u,
          H (t, stripPlaneMap g₀ v J F₀ (s, t)) =
            (t, stripPlaneMap g₁ v J F₁ (s, t))) ∧
        H '' ((fun z : Real × Real => (z.2, stripPlaneMap g₀ v J F₀ z)) ''
            (Icc l u ×ˢ Icc (-r) r)) =
          (fun z : Real × Real => (z.2, stripPlaneMap g₁ v J F₁ z)) ''
            (Icc l u ×ˢ Icc (-r) r) := by
  have hw : 0 < w := hr.trans hrw
  let f : Real × Real → E2 := fun z => Q (stripPlaneMap g₀ v J F₀ (z.2, z.1))
  let g : Real × Real → E2 := fun z => stripPlaneMap g₁ v J F₁ (z.2, z.1)
  let W : Set (Real × Real) := Ioo (-w) w ×ˢ Ioo (l - w) (u + w)
  obtain ⟨hf, hfi, hfd⟩ := projected_strip_interval_family_geometry hg₀ hv F₀ hw hrw
    hs₀ hF₀ hFi₀ hh₀ J Q
  obtain ⟨hg, hgi, hgd⟩ := projected_strip_interval_family_geometry hg₁ hv F₁ hw hrw
    hs₁ hF₁ hFi₁ hh₁ J (Diffeomorph.refl (𝓡 2) E2 ∞)
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_Ioo
  have hrect : Icc (-r) r ×ˢ Icc l u ⊆ W := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hF₀source (t s : Real) (ht : t ∈ Icc (-r) r) (hs : s ∈ Icc l u) :
      (s, t) ∈ F₀.source := by
    rw [hs₀]
    exact ⟨(hrect (a := (t, s)) ⟨ht, hs⟩).2, (hrect (a := (t, s)) ⟨ht, hs⟩).1⟩
  have hF₁source (t s : Real) (ht : t ∈ Icc (-r) r) (hs : s ∈ Icc l u) :
      (s, t) ∈ F₁.source := by
    rw [hs₁]
    exact ⟨(hrect (a := (t, s)) ⟨ht, hs⟩).2, (hrect (a := (t, s)) ⟨ht, hs⟩).1⟩
  obtain ⟨K, V₀, hK, hKU, hV₀, hendsV₀, D, hD₀, hD, hDfix, hDfixV, hDmatch⟩ :=
    exists_centered_relative_matching_of_interval_families hr
      hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u hU f g hW hrect hf hg hfi hgi hfd hgd
      hcentral hends (fun t ht s hs =>
        hproject₀ _ (F₀.map_source (hF₀source t s ht hs))) (fun t ht s hs =>
        hproject₁ _ (F₁.map_source (hF₁source t s ht hs)))
  let ρ := (r + R) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨L, hLt, hL, _, hLfix⟩ :=
    exists_supported_family_suspension D hD hD₀ hK hDfix (hr.trans hrρ) hρR
  let Qlift : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞ := {
    toEquiv := (Equiv.refl Real).prodCongr Q.toEquiv
    contMDiff_toFun := (contDiff_fst.prodMk
      (Q.contMDiff.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (Q.symm.contMDiff.contDiff.comp contDiff_snd)).contMDiff }
  let H := Qlift.trans L
  let V : Set P2 := Qlift ⁻¹' (V₀ ∩ (Ioo (-ρ) ρ ×ˢ (univ : Set E2)))
  have hV : IsOpen V :=
    (hV₀.inter (isOpen_Ioo.prod isOpen_univ)).preimage Qlift.contMDiff.continuous
  have htρ (t : Real) (ht : t ∈ Icc (-r) r) : t ∈ Ioo (-ρ) ρ :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hclosed (t : Real) (ht : t ∈ Ioo (-ρ) ρ) : t ∈ closedBall (0 : Real) ρ := by
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact (abs_lt.mpr ht).le
  have hmatch (t : Real) (ht : t ∈ Icc (-r) r) (s : Real) (hs : s ∈ Icc l u) :
      H (t, stripPlaneMap g₀ v J F₀ (s, t)) = (t, stripPlaneMap g₁ v J F₁ (s, t)) := by
    change L (t, f (t, s)) = (t, g (t, s))
    rw [hL t (hclosed t (htρ t ht)), hDmatch t ht s hs]
  refine ⟨K, V, hK, hKU, hV, ?_, H, ?_, ?_, ?_, ?_, hmatch, ?_⟩
  · intro t ht s hs
    exact ⟨hendsV₀ t ht s hs, htρ t ht, mem_univ _⟩
  · intro z
    exact hLt (Qlift z)
  · intro x
    change L (0, Q x) = (0, Q x)
    rw [hL 0 (mem_closedBall_self (hr.trans hrρ).le), hD₀]
  · intro z hz
    exact hLfix (Qlift z) hz
  · rintro ⟨t, x⟩ ⟨hz, ht, _⟩
    change L (t, Q x) = (t, Q x)
    rw [hL t (hclosed t ht), hDfixV t (Q x) hz]
  · apply Subset.antisymm
    · rintro _ ⟨_, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩, rfl⟩
      exact ⟨(s, t), ⟨hs, ht⟩, (hmatch t ht s hs).symm⟩
    · rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
      exact ⟨_, ⟨(s, t), ⟨hs, ht⟩, rfl⟩, hmatch t ht s hs⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
