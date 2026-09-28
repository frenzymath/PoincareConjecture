import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.TimeClamp
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Suspension



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1




theorem exists_circle_family_flattening_with_constant_ends
    {a b w : Real} (hw : 0 < w) (hsep : a + w < b - w)
    (γ : Real × S1 → E2)
    (hγ : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ γ)
    (hemb : ∀ t ∈ Icc a b,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (fun q => γ (t, q)))
    (hleft : ∀ t ∈ Icc a (a + w), range (fun q => γ (t, q)) = range (fun q => γ (a, q)))
    (hright : ∀ t ∈ Icc (b - w) b, range (fun q => γ (t, q)) = range (fun q => γ (b, q))) :
    ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      Q '' range (fun q => γ (b, q)) = range (fun q => γ (a, q)) ∧
      ∃ S : Set E2, IsCompact S ∧
      ∃ D : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
          (Real × E2) (Real × E2) ∞,
        (∀ z, (D z).1 = z.1) ∧
        (∀ t x, t ≤ a + w / 4 → D (t, x) = (t, x)) ∧
        (∀ t x, b - w / 4 ≤ t → D (t, x) = (t, Q x)) ∧
        (∀ t x, x ∉ S → D (t, x) = (t, x)) ∧
        (∀ t ∈ Icc a b,
          D '' ({t} ×ˢ range (fun q => γ (t, q))) =
            {t} ×ˢ range (fun q => γ (a, q))) ∧
        D '' ((fun z : Real × S1 => (z.1, γ z)) '' (Icc a b ×ˢ univ)) =
          Icc a b ×ˢ range (fun q => γ (a, q)) := by
  have hab : a ≤ b := by linarith
  obtain ⟨θ, hθ, hθrange, hθleft, hθright, hθpieces⟩ :=
    exists_smooth_band_endpoint_clamp hw hsep
  obtain ⟨Φ, hΦ0, hΦ, ⟨S, hS, hΦfix⟩, hΦmotion⟩ :=
    exists_ambient_isotopy_of_circle_isotopy hab γ hγ hemb
  have hθimage (t : Real) (ht : t ∈ Icc a b) :
      range (fun q => γ (θ t, q)) = range (fun q => γ (t, q)) := by
    rcases hθpieces t ht with ⟨htl, hθl⟩ | ⟨htr, hθr⟩ | hθt
    · exact (hleft _ hθl).trans (hleft _ htl).symm
    · exact (hright _ hθr).trans (hright _ htr).symm
    · rw [hθt]
  have himage (t : Real) (ht : t ∈ Icc a b) :
      Φ (θ t) '' range (fun q => γ (a, q)) = range (fun q => γ (t, q)) := by
    rw [← hθimage t ht, ← range_comp]
    congr 1
    funext q
    exact hΦmotion _ (hθrange t) q
  have hslice (t : Real) (ht : t ∈ Icc a b) :
      (Φ (θ t)).symm '' range (fun q => γ (t, q)) = range (fun q => γ (a, q)) := by
    rw [← himage t ht, ← image_comp]
    simp only [Function.comp_def, Diffeomorph.symm_apply_apply, image_id']
  have hΦm : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × E2 => Φ z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hΦ.contMDiff
  have hΦi := Poincare.Manifold.contMDiff_diffeomorph_family_symm Φ hΦm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hΦi
  let D : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
      (Real × E2) (Real × E2) ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, (Φ (θ z.1)).symm z.2)
      invFun := fun z => (z.1, Φ (θ z.1) z.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
    contMDiff_toFun := (contDiff_fst.prodMk
      (hΦi.contDiff.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd))).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (hΦ.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd))).contMDiff }
  have hDslices (t : Real) (ht : t ∈ Icc a b) :
      D '' ({t} ×ˢ range (fun q => γ (t, q))) =
        {t} ×ˢ range (fun q => γ (a, q)) := by
    ext z
    constructor
    · rintro ⟨⟨u, x⟩, ⟨hu, hx⟩, rfl⟩
      have hut : u = t := hu
      subst u
      exact ⟨rfl, hslice t ht ▸ mem_image_of_mem (Φ (θ t)).symm hx⟩
    · rintro ⟨hz, hx⟩
      obtain ⟨x, hx, hxx⟩ := (hslice t ht).symm ▸ hx
      refine ⟨(t, x), ⟨rfl, hx⟩, ?_⟩
      exact Prod.ext hz.symm hxx
  refine ⟨(Φ b).symm, ?_, S, hS, D, fun _ => rfl, ?_, ?_, ?_, hDslices, ?_⟩
  · have := hslice b ⟨hab, le_rfl⟩
    rwa [hθright b (by linarith)] at this
  · intro t x ht
    change (t, (Φ (θ t)).symm x) = (t, x)
    rw [hθleft t ht]
    congr 1
    apply (Φ a).injective
    change Φ a ((Φ a).symm x) = Φ a x
    rw [(Φ a).apply_symm_apply, hΦ0]
  · intro t x ht
    change (t, (Φ (θ t)).symm x) = (t, (Φ b).symm x)
    rw [hθright t ht]
  · intro t x hx
    change (t, (Φ (θ t)).symm x) = (t, x)
    congr 1
    apply (Φ (θ t)).injective
    change Φ (θ t) ((Φ (θ t)).symm x) = Φ (θ t) x
    rw [(Φ (θ t)).apply_symm_apply, hΦfix _ _ hx]
  · ext z
    constructor
    · rintro ⟨_, ⟨⟨t, q⟩, ⟨ht, _⟩, rfl⟩, rfl⟩
      exact ⟨ht, hslice t ht ▸ mem_image_of_mem (Φ (θ t)).symm (mem_range_self q)⟩
    · rintro ⟨ht, hx⟩
      obtain ⟨x, ⟨q, rfl⟩, hqx⟩ := (hslice z.1 ht).symm ▸ hx
      refine ⟨(z.1, γ (z.1, q)), ⟨(z.1, q), ⟨ht, mem_univ _⟩, rfl⟩, ?_⟩
      exact Prod.ext rfl hqx

end Poincare.Manifold.Schoenflies
