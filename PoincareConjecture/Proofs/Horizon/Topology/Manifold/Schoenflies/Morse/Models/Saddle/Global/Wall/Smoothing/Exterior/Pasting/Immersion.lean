import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.AnchorCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.StripAnchorCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.CorrectedStrip

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IR" => 𝓘(Real, Real)
local notation "IR2" => 𝓘(Real, Real × Real)

def projectedPastedRoundedAnchor {v : E3} (g : S2 → E3)
    (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (t₀ : Real) (α : S1 → S2)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) (x θ : Real → Real)
    (U : Set S2) (z : Real × S1) : E2 :=
  planarProjection J (D (pastedRoundedAnchor g e F R t₀ α D J c H x θ U z))

theorem projectedPastedRoundedAnchor_of_mem
    {v : E3} (g : S2 → E3) (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (t₀ : Real) (α : S1 → S2)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) (x θ : Real → Real)
    {U : Set S2} {t : Real} {q : S1} (hq : α q ∈ U) :
    projectedPastedRoundedAnchor g e F R t₀ α D J c H x θ U (t, q) =
      sliceParam H x (θ t) (e.symm (α q) 1) := by
  simp only [projectedPastedRoundedAnchor, pastedRoundedAnchor, if_pos hq,
    roundedPatch, D.apply_symm_apply, planarProjection_graph]

theorem projectedPastedRoundedAnchor_of_not_mem
    {v : E3} (g : S2 → E3) (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (t₀ : Real) (α : S1 → S2)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) (x θ : Real → Real)
    {U : Set S2} {t : Real} {q : S1} (hq : α q ∉ U) :
    projectedPastedRoundedAnchor g e F R t₀ α D J c H x θ U (t, q) =
      correctedStrip g D J F R (θ t, anchorStripParameter F R t₀ α q) := by
  simp only [projectedPastedRoundedAnchor, pastedRoundedAnchor, if_neg hq,
    correctedStrip]

theorem projectedPastedRoundedAnchor_of_exterior
    {v : E3} (g : S2 → E3) (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (t₀ : Real) (α : S1 → S2)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) (x θ : Real → Real)
    {U V : Set S2} {t : Real}
    (hmatch : ∀ q, α q ∈ U ∩ V →
      roundedPatch D J c H x (θ t, e.symm (α q) 1) =
        g (F (R (θ t) (anchorStripParameter F R t₀ α q), θ t)))
    {q : S1} (hq : α q ∈ V) :
    projectedPastedRoundedAnchor g e F R t₀ α D J c H x θ U (t, q) =
      correctedStrip g D J F R (θ t, anchorStripParameter F R t₀ α q) := by
  classical
  by_cases hqU : α q ∈ U
  · simp only [projectedPastedRoundedAnchor, pastedRoundedAnchor, if_pos hqU,
      hmatch q ⟨hqU, hq⟩, correctedStrip]
  · exact projectedPastedRoundedAnchor_of_not_mem g e F R t₀ α D J c H x θ hqU

theorem injective_mfderiv_projectedPastedRoundedAnchor
    {v : E3} {g : S2 → E3}
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (R : Real → Real ≃ₘ[Real] Real)
    (hR : ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2))
    {c t₀ : Real} (ht₀ : t₀ < 0)
    (α : S1 → S2) (hα : ContMDiff (𝓡 1) (𝓡 2) ∞ α)
    (hαinj : Injective α)
    (hαder : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) α q))
    (hlevel : ∀ q, inner Real v (g (α q)) = c + t₀)
    (hform : ∀ u ∈ e.source, inner Real v (g (e u)) = c - (u 0)^2 + (u 1)^2)
    (hheight : ∀ z ∈ F.source, inner Real v (g (F z)) = c + z.2)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y, inner Real v (D y) = inner Real v y)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (H : Real ≃ₘ[Real] Real) {x θ : Real → Real}
    (hx : ContDiff Real ∞ x) {U V : Set S2}
    (hU : IsOpen U) (hV : IsOpen V) (hUe : U ⊆ e.target) (hVF : V ⊆ F.target)
    (hnegative : ∀ q, α q ∈ U → e.symm (α q) 0 < 0)
    (hcover : range α ⊆ U ∪ V) (t : Real)
    (hsource : ∀ q, α q ∈ V →
      (R (θ t) (anchorStripParameter F R t₀ α q), θ t) ∈ F.source)
    (hmatch : ∀ q, α q ∈ U ∩ V →
      roundedPatch D J c H x (θ t, e.symm (α q) 1) =
        g (F (R (θ t) (anchorStripParameter F R t₀ α q), θ t))) :
    ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2)
      (fun q => projectedPastedRoundedAnchor g e F R t₀ α D J c H x θ U (t, q)) q) := by
  have hlocal := negative_anchor_longitudinal_geometry
    (height := fun p => inner Real v (g p)) (c := c) ht₀ α hα hαinj hαder hlevel e he hei
    hform hU hUe hnegative
  have hext := strip_anchor_parameter_geometry
    (height := fun p => inner Real v (g p)) (c := c) α hα hαinj hαder hlevel
    F hF hFi hheight R hV hVF
  have hpreU : IsOpen (α ⁻¹' U) := hU.preimage hα.continuous
  have hpreV : IsOpen (α ⁻¹' V) := hV.preimage hα.continuous
  intro q
  by_cases hqU : α q ∈ U
  · have heq : (fun q =>
        projectedPastedRoundedAnchor g e F R t₀ α D J c H x θ U (t, q)) =ᶠ[𝓝 q]
        sliceParam H x (θ t) ∘ anchorLongitudinalCoordinate e α := by
      filter_upwards [hpreU.mem_nhds hqU] with z hz
      exact projectedPastedRoundedAnchor_of_mem g e F R t₀ α D J c H x θ hz
    have hs := sliceParam_isSmoothEmbedding H x hx (θ t)
    have hyq := hlocal.1.contMDiffAt (hpreU.mem_nhds hqU)
    rw [heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 2),
      mfderiv_comp q (hs.contMDiff.mdifferentiable (by simp) _)
        (hyq.mdifferentiableAt (by simp))]
    exact ((hs.isImmersion.isImmersionAt _).injective_mfderiv_modelWithCornersSelf
      (show (∞ : ℕ∞ω) ≠ 0 by simp)).comp (hlocal.2.2 q hqU)
  · have hqV : α q ∈ V := (hcover ⟨q, rfl⟩).resolve_left hqU
    let f : Real → E2 := fun s => correctedStrip g D J F R (θ t, s)
    have heq : (fun q =>
        projectedPastedRoundedAnchor g e F R t₀ α D J c H x θ U (t, q)) =ᶠ[𝓝 q]
        f ∘ anchorStripParameter F R t₀ α := by
      filter_upwards [hpreV.mem_nhds hqV] with z hz
      exact projectedPastedRoundedAnchor_of_exterior g e F R t₀ α D J c H x θ hmatch hz
    have hopen : IsOpen ((fun z : Real × Real => (R z.1 z.2, z.1)) ⁻¹' F.source) :=
      F.open_source.preimage (hR.continuous.prodMk continuous_fst)
    have hfull := contDiffOn_correctedStrip hg D J F hF R hR
    have hfs : ContDiffAt Real ∞ f (anchorStripParameter F R t₀ α q) :=
      (hfull.contDiffAt (hopen.mem_nhds (hsource q hqV))).comp _
        (contDiff_const.prodMk contDiff_id).contDiffAt
    have hfd : Injective (mfderiv IR (𝓡 2) f (anchorStripParameter F R t₀ α q)) := by
      have hd := (correctedStrip_slice_geometry hg hv D hDheight J F hF hFi hheight R hR
        (θ t)).2 _ (hsource q hqV)
      rw [mfderiv_eq_fderiv]
      change Injective (fderiv Real f (anchorStripParameter F R t₀ α q))
      intro a b hab
      apply smul_left_injective Real hd
      simpa only [fderiv_eq_smul_deriv] using hab
    have hσq := hext.1.contMDiffAt (hpreV.mem_nhds hqV)
    rw [heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 2),
      mfderiv_comp q (hfs.contMDiffAt.mdifferentiableAt (by simp))
        (hσq.mdifferentiableAt (by simp))]
    exact hfd.comp (hext.2.2 q hqV)

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
