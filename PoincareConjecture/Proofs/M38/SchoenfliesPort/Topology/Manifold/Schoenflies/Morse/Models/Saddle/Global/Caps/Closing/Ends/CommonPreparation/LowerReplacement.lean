import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.Cylindrical
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CylindricalPreparation
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Normalization
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.RelativeAlignment
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.AxisReversal







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap Poincare.Geometry.Euclidean _root_.Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

set_option maxHeartbeats 1500000 in




theorem exists_buffered_relative_lower_end_replacement_of_surface_germ
    {v : E3} {g f : S2 → E3} {Z : Set Real}
    {D : SphereSurgeryCoreCap v g Z} {C₀ : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C₀ h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) (hDb : D.center < b)
    (hgerm : ∀ p ∈ C₀, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1)
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (seed : S2)
    (hcomponent : d '' closedBall 0 1 =
      closure (connectedComponentIn ((fun q => inner Real v (f q)) ⁻¹' Iio b) seed))
    (hregular : ∀ q, inner Real v (f q) = b →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) q ≠ 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) + ‖x‖ ^ 2)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn IP (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) IP ∞ T.symm T.target)
    {ε : Real} (hε : 0 < ε)
    (hTs : univ ×ˢ Icc (b - ε) (b + ε) ⊆ T.source)
    (hTh : ∀ q z, z ∈ Icc (b - ε) (b + ε) → inner Real v (f (T (q, z))) = z)
    (hTc : range (fun q : S1 => T (q, b)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q z, z ∈ Ioo (b - ε) b → T (q, z) ∈ d '' ball (0 : E2) 1)
    (hrim : range (fun q : S1 => g (A.chart (q, b))) =
      range (fun q : S1 => f (T (q, b))))
    {U : Set E3} (hU : IsOpen U)
    (hrimU : range (fun q : S1 => g (A.chart (q, b))) ⊆ U)
    (hsurface : range g ∩ U = range f ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧ (∃ η : Real, 0 < η ∧ EqOn F id {y | b - η ≤ inner Real v y}) ∧
        F '' (g '' A.cappedRegion b) = f '' (d '' closedBall 0 1) := by
  obtain ⟨εa, hεa, hAs, hAh⟩ :=
    A.exists_physical_height_at_terminal (haD.trans hDb.le) hDb.le hgerm
  let ε₀ := min εa ε
  have hε₀ : 0 < ε₀ := lt_min hεa hε
  have hε₀a : ε₀ ≤ εa := min_le_left _ _
  have hε₀m : ε₀ ≤ ε := min_le_right _ _
  have hsuba : Icc (b - ε₀) (b + ε₀) ⊆ Icc (b - εa) (b + εa) := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hsubm : Icc (b - ε₀) (b + ε₀) ⊆ Icc (b - ε) (b + ε) := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨r, δ, hr, _, hδ, _, _, Q, C, hQheight, ⟨Kq, hKq, hKslab, hQfix⟩,
    hcentral, hCs, _, hCcyl, hCrim, hCinside, hconstant⟩ :=
    exists_common_cylindrical_preparation_of_surface_germ D.unit_v hg.isEmbedding hf d
      A.chart T hT hTi hε₀ (half_pos (sub_pos.mpr hDb))
      (fun z hz => hAs ⟨hz.1, hsuba hz.2⟩)
      (fun z hz => hTs ⟨hz.1, hsubm hz.2⟩)
      (fun q z hz => hAh q z (hsuba hz)) (fun q z hz => hTh q z (hsubm hz))
      hTc (fun q z hz => hTneg q z ⟨by linarith [hz.1], hz.2⟩)
      hrim hU hrimU hsurface
  have hcore : EqOn (Q ∘ g) g (D.chart '' closedBall (0 : E2) 1) := by
    intro p hp
    apply hQfix
    intro hmem
    have hs : |inner Real v (g p) - b| ≤ (b - D.center) / 2 := hKslab hmem
    have hh := (abs_le.mp hs).1
    have hlow := A.height_le_center_of_mem_cap hp
    change -( (b - D.center) / 2) ≤ inner Real v (g p) - b at hh
    linarith
  let g' : S2 → E3 := Q ∘ g
  let f' : S2 → E3 := Q ∘ f
  let A' := A.congrEmbedding hcore (fun q => hQheight (g q))
  have hchart : A'.chart = A.chart := rfl
  have hcap : A'.cappedRegion b = A.cappedRegion b := rfl
  have hemb (k : S2 → E3) (hk : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ k) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (Q ∘ k) := by
    apply isSmoothEmbedding_of_injective_mfderiv (Q.contMDiff.comp hk.contMDiff)
      (Q.injective.comp hk.isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (Q.contMDiff.mdifferentiable (by simp) _)
      (hk.contMDiff.mdifferentiable (by simp) _)]
    exact (Q.mfderivToContinuousLinearEquiv (by simp) (k q)).injective.comp
      (injective_mfderiv_sphere_embedding hk q)
  have hgerm' : ∀ p ∈ C₀, h =ᶠ[𝓝 p] (fun q => inner Real v (g' q)) := by
    simpa only [g', Function.comp_apply, hQheight] using hgerm
  have hQrim (q : S1) : Q (g (A.chart (q, b))) = g (A.chart (q, b)) :=
    hcentral (A.actual_height q b ⟨hDb.le, le_rfl⟩)
  have hc : ∀ z ∈ Icc (b - δ) b,
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto (g' (A'.chart (q, z)))) =
      range (fun q : S1 =>
        (Hemisphere.Plane v).orthogonalProjectionOnto (g' (A'.chart (q, b)))) := by
    intro z hz
    simpa only [g', Function.comp_apply, hchart, hQrim] using
      hconstant z ⟨hz.1, by linarith [hz.2]⟩
  obtain ⟨da, u, hda, hu, _, _, Ba, Ka, hKa, Na, hBa, hNafix, hNahalf, hNaimage⟩ :=
    exists_supported_cylindrical_lower_terminal_end_normalization A' (hemb g hg)
      haD hDb hgerm' hδ hc
  have hphysical : (fun q => inner Real v ((Q ∘ f) q)) = fun q => inner Real v (f q) :=
    funext (fun q => hQheight (f q))
  let γ : S1 → Hemisphere.Plane v := fun q =>
    (Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, b)))
  obtain ⟨dm, sm, hsm, hdm, Bm, Km, hKm, Nm, hBm, hNmfix, ⟨δm, hδm, hNmhalf⟩, hNmimage⟩ :=
    exists_buffered_relative_component_minimum_disk_normalization (hemb f hf) D.unit_v d hds hp
      (by simpa only [Function.comp_apply, hQheight] using hpb)
      (by simpa only [Function.comp_apply, hQheight] using hboundary)
      (by rw [hphysical]; exact hunique) seed
      (by simpa only [Function.comp_apply, hQheight] using hcomponent)
      (by
        intro q hq
        rw [hphysical]
        exact hregular q ((hQheight _).symm.trans hq)) e he0 hep he hei
      (by simpa only [Function.comp_apply, hQheight] using hform) hr
      C hCs γ hCcyl hCrim hCinside
  have hrange : range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
      (g (A.chart (q, b)))) = range γ := by
    have hh := congrArg (fun S : Set E3 => (Hemisphere.Plane v).orthogonalProjectionOnto '' S) hrim
    rw [← range_comp, ← range_comp] at hh
    exact hh
  have hBacircle : (D.planeMap.trans Ba.symm) '' sphere (0 : Hemisphere.Plane v) 1 = range γ := by
    simpa only [congrEmbedding, hchart, Function.comp_apply, hQrim, hrange] using hBa
  obtain ⟨hcircle, hcinj, hcder⟩ := AnnularEndFamily.annular_slice_geometry T hT hTi b
    (fun q => hTs ⟨mem_univ _, by linarith, by linarith⟩)
  have hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ :=
    AnnularEndFamily.projected_circle_embedding hf D.unit_v _ hcircle hcinj hcder
      (fun q => hTh q b ⟨by linarith, by linarith⟩)
  let Fa := Q.trans Na
  let Fm := Q.trans Nm
  have hcompact (N : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (K : Set E3)
      (hK : IsCompact K) (hfix : ∀ y ∉ K, N y = y) :
      ∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, (Q.trans N) y = y := by
    refine ⟨Kq ∪ K, hKq.union hK, ?_⟩
    intro y hy
    change N (Q y) = y
    rw [hQfix y (fun hh => hy (Or.inl hh)), hfix y (fun hh => hy (Or.inr hh))]
  let w := min (u / 4) δm
  have hw : 0 < w := lt_min (by linarith) hδm
  have hwu : w ≤ u / 4 := min_le_left _ _
  have hwm : w ≤ δm := min_le_right _ _
  have hFa (y : E3) (hy : b - w ≤ inner Real v y) : Fa y = Q y := by
    apply hNahalf
    change b - u / 4 ≤ inner Real v (Q y)
    rw [hQheight]
    linarith
  have hFm (y : E3) (hy : b - w ≤ inner Real v y) : Fm y = Q y :=
    hNmhalf (Q y) (by rw [hQheight]; linarith)
  have hFaimage : Fa '' (g '' A.cappedRegion b) =
      liftPlaneDiffeomorph D.unit_v da D.scale A.scale_neg.ne
        (D.planeMap.trans Ba.symm) '' boundedCylinderNorthernCap v ∪
        terminalCylinder (range γ) da b := by
    rw [terminalCylinder_eq_height_product]
    simpa only [Fa, Diffeomorph.coe_trans, g', image_image, Function.comp_apply,
      hcap, hchart, hQrim, congrEmbedding, hrange] using hNaimage
  have hFmimage : Fm '' (f '' (d '' closedBall 0 1)) =
      liftPlaneDiffeomorph D.unit_v dm sm hsm.ne Bm '' boundedCylinderNorthernCap v ∪
        terminalCylinder (range γ) dm b := by
    rw [terminalCylinder_eq_height_product]
    simpa only [Fm, Diffeomorph.coe_trans, f', image_image, Function.comp_apply] using hNmimage
  exact exists_buffered_relative_cap_alignment_of_compatible_normalizations D.unit_v γ hγ
    (D.planeMap.trans Ba.symm) Bm hBacircle hBm (hda.trans hDb) hdm A.scale_neg hsm Fa Fm
    (hcompact Na Ka hKa hNafix) (hcompact Nm Km hKm hNmfix) hw
    (fun y hy => (hFa y hy).trans (hFm y hy).symm)
    (fun y hy => by rw [hFa y hy, hQheight]) hFaimage hFmimage

set_option maxHeartbeats 1500000 in


theorem exists_relative_lower_end_replacement_of_surface_germ
    {v : E3} {g f : S2 → E3} {Z : Set Real}
    {D : SphereSurgeryCoreCap v g Z} {C₀ : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C₀ h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) (hDb : D.center < b)
    (hgerm : ∀ p ∈ C₀, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1)
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (seed : S2)
    (hcomponent : d '' closedBall 0 1 =
      closure (connectedComponentIn ((fun q => inner Real v (f q)) ⁻¹' Iio b) seed))
    (hregular : ∀ q, inner Real v (f q) = b →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) q ≠ 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) + ‖x‖ ^ 2)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn IP (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) IP ∞ T.symm T.target)
    {ε : Real} (hε : 0 < ε)
    (hTs : univ ×ˢ Icc (b - ε) (b + ε) ⊆ T.source)
    (hTh : ∀ q z, z ∈ Icc (b - ε) (b + ε) → inner Real v (f (T (q, z))) = z)
    (hTc : range (fun q : S1 => T (q, b)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q z, z ∈ Ioo (b - ε) b → T (q, z) ∈ d '' ball (0 : E2) 1)
    (hrim : range (fun q : S1 => g (A.chart (q, b))) =
      range (fun q : S1 => f (T (q, b))))
    {U : Set E3} (hU : IsOpen U)
    (hrimU : range (fun q : S1 => g (A.chart (q, b))) ⊆ U)
    (hsurface : range g ∩ U = range f ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧ EqOn F id {y | b ≤ inner Real v y} ∧
        F '' (g '' A.cappedRegion b) = f '' (d '' closedBall 0 1) := by
  obtain ⟨K, hK, F, hF, ⟨η, hη, hu⟩, hi⟩ :=
    exists_buffered_relative_lower_end_replacement_of_surface_germ A hg haD hDb hgerm
      hf d hds hp hpb hboundary hunique seed hcomponent hregular e he0 hep he hei hform
      T hT hTi hε hTs hTh hTc hTneg hrim hU hrimU hsurface
  refine ⟨K, hK, F, hF, ?_, hi⟩
  intro y hy
  apply hu
  change b - η ≤ inner Real v y
  change b ≤ inner Real v y at hy
  linarith

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
