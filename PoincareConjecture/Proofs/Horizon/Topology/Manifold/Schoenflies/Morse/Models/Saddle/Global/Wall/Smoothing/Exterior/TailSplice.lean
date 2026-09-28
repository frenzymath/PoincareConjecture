import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Profile
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Slices
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Normalization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem sliceParam_eq_of_left_tail
    (H : Real ≃ₘ[Real] Real) {ρ : Real → Real} {δ : Real} (hδ : 0 < δ)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hH : ∀ s, H s = profileHeight ρ s)
    {u : E2} {t : Real} (hu : u 0 ≤ -δ)
    (hlevel : -(u 0)^2 + (u 1)^2 = t) :
    sliceParam H (profileX ρ) t (u 1) = u := by
  have hHu : H (u 0) = t - (u 1)^2 := by
    rw [hH, profileHeight_of_le hδ htail hu]
    linarith
  have hinv : H.symm (t - (u 1)^2) = u 0 := by
    rw [← hHu, H.symm_apply_apply]
  ext i
  fin_cases i
  · change profileX ρ (H.symm (t - (u 1)^2)) = u 0
    rw [hinv, profileX_of_le hδ htail hu]
  · rfl

def roundedPatch {v : E3}
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) (x : Real → Real) (ty : Real × Real) : E3 :=
  D.symm ((J (sliceParam H x ty.1 ty.2) : E3) + (c + ty.1) • v)

theorem contDiff_roundedPatch {v : E3}
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) {x : Real → Real} (hx : ContDiff Real ∞ x) :
    ContDiff Real ∞ (roundedPatch D J c H x) :=
  D.symm.contDiff.comp
    ((((Real ∙ v)ᗮ.subtypeL.contDiff).comp
      (J.contDiff.comp (contDiff_sliceParam H x hx))).add
      ((contDiff_const.add contDiff_fst).smul contDiff_const))

theorem roundedPatch_eq_actual_of_left_tail
    {g : S2 → E3} (e : OpenPartialHomeomorph E2 S2) {v : E3} {c : Real}
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (H : Real ≃ₘ[Real] Real) {ρ : Real → Real} {δ : Real} (hδ : 0 < δ)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hH : ∀ s, H s = profileHeight ρ s)
    {u : E2} (hu : u 0 ≤ -δ)
    (hgraph : D (g (e u)) = (J u : E3) + (c - (u 0)^2 + (u 1)^2) • v) :
    roundedPatch D J c H (profileX ρ) (-(u 0)^2 + (u 1)^2, u 1) = g (e u) := by
  unfold roundedPatch
  rw [sliceParam_eq_of_left_tail H hδ htail hH hu rfl]
  have hh : c + (-(u 0)^2 + (u 1)^2) = c - (u 0)^2 + (u 1)^2 := by ring
  rw [hh, ← hgraph, D.symm_apply_apply]

theorem exists_actual_rounded_patch_splice
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ u ∈ e.source, inner Real v (g (e u)) =
      inner Real v (g p) - (u 0)^2 + (u 1)^2) :
    ∃ (a δ : Real) (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
        (A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
          (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞)
        (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
        (ρ : Real → Real) (H : Real ≃ₘ[Real] Real),
      0 < a ∧ 0 < δ ∧ 2 * δ < a ∧ closedBall (0 : E2) a ⊆ e.source ∧
      ContDiff Real ∞ ρ ∧ LipschitzWith 1 ρ ∧ (∀ s, |s| ≤ ρ s) ∧
      (∀ s, δ ≤ |s| → ρ s = |s|) ∧
      (∀ s, H s = profileHeight ρ s) ∧ StrictMono H ∧
      (∀ y, inner Real v (D y) = inner Real v y) ∧
      (∀ (t : Real) (z : (Real ∙ v)ᗮ),
        D (t • v + (z : E3)) = t • v + (A z : E3)) ∧
      (∀ u ∈ closedBall (0 : E2) a, D (g (e u)) =
        (J u : E3) + (inner Real v (g p) - (u 0)^2 + (u 1)^2) • v) ∧
      ContDiff Real ∞ (roundedPatch D J (inner Real v (g p)) H (profileX ρ)) ∧
      ∀ u ∈ closedBall (0 : E2) a, u 0 ≤ -δ →
        roundedPatch D J (inner Real v (g p)) H (profileX ρ)
          (-(u 0)^2 + (u 1)^2, u 1) = g (e u) := by
  obtain ⟨J, a, ha, has, A, D, hDheight, hDplane, hgraph, hrest⟩ :=
    SaddleLevel.exists_normalized_exterior_noncrossing_square hg hv p e he0 hep he hei
      hform (show (0 : Real) < 1 by norm_num)
  let δ := a / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδa : 2 * δ < a := by dsimp [δ]; linarith
  obtain ⟨ρ, H, hρ, hLip, hbound, hderiv, htail, hH, hmono, hHderiv, hHneg, hHpos⟩ :=
    exists_smooth_profile hδ
  refine ⟨a, δ, J, A, D, ρ, H, ha, hδ, hδa, has, hρ, hLip, fun s => (hbound s).1,
    htail, hH, hmono, hDheight, hDplane, hgraph,
    contDiff_roundedPatch D J (inner Real v (g p)) H (contDiff_profileX hρ), ?_⟩
  intro u hu huδ
  exact roundedPatch_eq_actual_of_left_tail e D J H hδ htail hH huδ (hgraph u hu)

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
