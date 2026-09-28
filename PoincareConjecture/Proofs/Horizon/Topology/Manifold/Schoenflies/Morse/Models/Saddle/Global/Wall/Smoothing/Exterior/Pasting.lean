import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Cover









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IR" => 𝓘(Real, Real)
local notation "IR2" => 𝓘(Real, Real × Real)
local notation "IP" => ModelWithCorners.prod 𝓘(Real, Real) (𝓡 1)

def anchorStripParameter (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (t₀ : Real) (α : S1 → S2) (q : S1) : Real :=
  (R t₀).symm (F.symm (α q)).1


def pastedRoundedAnchor {v : E3} (g : S2 → E3)
    (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (t₀ : Real) (α : S1 → S2)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) (x : Real → Real) (θ : Real → Real)
    (U : Set S2) (z : Real × S1) : E3 := by
  classical
  exact if α z.2 ∈ U then
    roundedPatch D J c H x (θ z.1, e.symm (α z.2) 1)
  else g (F (R (θ z.1) (anchorStripParameter F R t₀ α z.2), θ z.1))



theorem roundedPatch_eq_strip_of_tail_transport
    {g : S2 → E3} (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2) {v : E3} {c : Real}
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (H : Real ≃ₘ[Real] Real) {ρ : Real → Real} {δ t s y u : Real}
    (hδ : 0 < δ) (htail : ∀ z, δ ≤ |z| → ρ z = |z|)
    (hH : ∀ z, H z = profileHeight ρ z)
    (hy : y = tailCoordinate e F s)
    (hcoord : rawTailCoordinates e F (t, s) 0 ≤ -δ)
    (hlevel : -(rawTailCoordinates e F (t, s) 0)^2 +
      (rawTailCoordinates e F (t, s) 1)^2 = t)
    (hgraph : D (g (e (rawTailCoordinates e F (t, s)))) =
      (J (rawTailCoordinates e F (t, s)) : E3) +
        (c - (rawTailCoordinates e F (t, s) 0)^2 +
          (rawTailCoordinates e F (t, s) 1)^2) • v)
    (hmotion : F (u, t) = rawTailPoint e F (t, s)) :
    roundedPatch D J c H (profileX ρ) (t, y) = g (F (u, t)) := by
  have h := roundedPatch_eq_actual_of_left_tail e D J H hδ htail hH hcoord hgraph
  rw [hlevel] at h
  change roundedPatch D J c H (profileX ρ) (t, tailCoordinate e F s) =
    g (rawTailPoint e F (t, s)) at h
  simpa only [hy, hmotion] using h



theorem contMDiff_pastedRoundedAnchor
    {v : E3} {g : S2 → E3} (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g)
    (e : OpenPartialHomeomorph E2 S2)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (R : Real → Real ≃ₘ[Real] Real)
    (hR : ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2))
    (t₀ : Real) (α : S1 → S2) (hα : ContMDiff (𝓡 1) (𝓡 2) ∞ α)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) {x θ : Real → Real}
    (hx : ContDiff Real ∞ x) (hθ : ContDiff Real ∞ θ)
    {U V : Set S2} (hU : IsOpen U) (hV : IsOpen V)
    (hUe : U ⊆ e.target) (hVF : V ⊆ F.target) (hcover : range α ⊆ U ∪ V)
    (hsource : ∀ t q, α q ∈ V →
      (R (θ t) (anchorStripParameter F R t₀ α q), θ t) ∈ F.source)
    (hmatch : ∀ t q, α q ∈ U ∩ V →
      roundedPatch D J c H x (θ t, e.symm (α q) 1) =
        g (F (R (θ t) (anchorStripParameter F R t₀ α q), θ t))) :
    ContMDiff IP (𝓡 3) ∞ (pastedRoundedAnchor g e F R t₀ α D J c H x θ U) := by
  classical
  let A : Set (Real × S1) := (fun z : Real × S1 => α z.2) ⁻¹' U
  let B : Set (Real × S1) := (fun z : Real × S1 => α z.2) ⁻¹' V
  let f : Real × S1 → E3 := fun z =>
    roundedPatch D J c H x (θ z.1, e.symm (α z.2) 1)
  let k : Real × S1 → E3 := fun z =>
    g (F (R (θ z.1) (anchorStripParameter F R t₀ α z.2), θ z.1))
  have hαp : ContMDiff IP (𝓡 2) ∞ (fun z : Real × S1 => α z.2) :=
    hα.comp contMDiff_snd
  have hA : IsOpen A := hU.preimage hαp.continuous
  have hB : IsOpen B := hV.preimage hαp.continuous
  have hθp : ContMDiff IP IR ∞ (fun z : Real × S1 => θ z.1) :=
    hθ.contMDiff.comp contMDiff_fst
  have heα : ContMDiffOn IP (𝓡 2) ∞ (fun z : Real × S1 => e.symm (α z.2)) A :=
    hei.comp hαp.contMDiffOn (fun z hz => hUe hz)
  have hy : ContMDiffOn IP IR ∞ (fun z : Real × S1 => e.symm (α z.2) 1) A :=
    (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contMDiff.comp_contMDiffOn heα
  have hpair : ContMDiffOn IP IR2 ∞
      (fun z : Real × S1 => (θ z.1, e.symm (α z.2) 1)) A := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hθp.contMDiffOn.prodMk hy
  have hf : ContMDiffOn IP (𝓡 3) ∞ f A :=
    (contDiff_roundedPatch D J c H hx).contMDiff.comp_contMDiffOn hpair
  have hFα : ContMDiffOn IP IR2 ∞ (fun z : Real × S1 => F.symm (α z.2)) B :=
    hFi.comp hαp.contMDiffOn (fun z hz => hVF hz)
  have hσ : ContMDiffOn IP IR ∞
      (fun z : Real × S1 => anchorStripParameter F R t₀ α z.2) B := by
    apply (R t₀).symm.contMDiff.comp_contMDiffOn
    exact (contDiff_fst : ContDiff Real ∞ (Prod.fst : Real × Real → Real)).contMDiff
      |>.comp_contMDiffOn hFα
  have hθσ : ContMDiffOn IP IR2 ∞
      (fun z : Real × S1 => (θ z.1, anchorStripParameter F R t₀ α z.2)) B := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hθp.contMDiffOn.prodMk hσ
  have hRσ := hR.contMDiff.comp_contMDiffOn hθσ
  have hextpair : ContMDiffOn IP IR2 ∞ (fun z : Real × S1 =>
      (R (θ z.1) (anchorStripParameter F R t₀ α z.2), θ z.1)) B := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hRσ.prodMk hθp.contMDiffOn
  have hk : ContMDiffOn IP (𝓡 3) ∞ k B := hg.comp_contMDiffOn
    (hF.comp hextpair (fun z hz => hsource z.1 z.2 hz))
  intro z
  by_cases hz : z ∈ A
  · apply (hf.contMDiffAt (hA.mem_nhds hz)).congr_of_eventuallyEq
    filter_upwards [hA.mem_nhds hz] with w hw
    change α w.2 ∈ U at hw
    simp only [pastedRoundedAnchor, if_pos hw]
    rfl
  · have hzB : z ∈ B := (hcover ⟨z.2, rfl⟩).resolve_left hz
    apply (hk.contMDiffAt (hB.mem_nhds hzB)).congr_of_eventuallyEq
    filter_upwards [hB.mem_nhds hzB] with w hw
    by_cases hwA : w ∈ A
    · change α w.2 ∈ U at hwA
      simp only [pastedRoundedAnchor, if_pos hwA]
      exact hmatch w.1 w.2 ⟨hwA, hw⟩
    · change α w.2 ∉ U at hwA
      simp only [pastedRoundedAnchor, if_neg hwA]
      rfl

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
