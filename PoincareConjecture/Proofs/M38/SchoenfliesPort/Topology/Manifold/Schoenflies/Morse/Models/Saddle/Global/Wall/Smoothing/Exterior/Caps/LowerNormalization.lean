import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.LowerBelt
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.TruncatedCap

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open SphereSurgeryCoreCap
open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem exists_lower_end_relative_normalization
    {v : E3} {g : S2 → E3} {P : Set Real}
    {D : SphereSurgeryCoreCap v g P} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) {c : Real} (hDc : D.center < c) (hcb : c < b)
    (hgerm : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
      h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ δ η : Real, 0 < δ ∧ 0 < η ∧ η < 1 ∧
      ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
        T.source = univ ×ˢ Ioo (D.center - δ) (c + δ) ∧
        ContMDiffOn IP (𝓡 2) ∞ T T.source ∧
        ContMDiffOn (𝓡 2) IP ∞ T.symm T.target ∧
        (∀ z, T z = A.chart z) ∧
        (∀ q t, t ∈ Ioo (D.center - δ) (c + δ) →
          inner Real v (g (T (q, t))) = t) ∧
        D.center + D.scale * η ∈ Ioo (D.center - δ) (c + δ) ∧
        (∀ θ ∈ Icc (0 : Real) η,
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (g (T (q, D.center + D.scale * θ)))) =
              D.planeMap '' sphere (0 : Hemisphere.Plane v) 1) ∧
        ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y : E3, (inner Real v y - D.center) / D.scale ≤
              (1 + η) / 2 → F y = y) ∧
          (∀ y : E3, D.center + D.scale * η ≤ inner Real v y →
            (fun z => F z) =ᶠ[𝓝 y] id) ∧
          (∀ y : E3, (Hemisphere.Plane v).orthogonalProjectionOnto (F y) =
            (Hemisphere.Plane v).orthogonalProjectionOnto y) ∧
          F '' (g '' A.cappedRegion c) =
            (liftPlaneDiffeomorph D.unit_v
              (D.center + D.scale * η) D.scale D.scale_ne_zero D.planeMap ''
                boundedCylinderNorthernCap v) ∪
              g '' (T '' (univ ×ˢ Icc (D.center + D.scale * η) c)) ∧
          (∀ y ∈ g '' (T '' (univ ×ˢ
              Icc (D.center + D.scale * η) c)), F y = y) := by
  obtain ⟨δ, η, hδ, hη, hη1, T, hTs, hT, hTi, hTA, hheight,
      hcut, hdecomp, hcircles⟩ :=
    exists_lower_end_truncated_cap_decomposition A hg haD hDc hcb hgerm
  obtain ⟨φ, _, _, _, F, _, hproj, hfix, _, himage⟩ :=
    exists_ambient_truncated_cap_normalization D.unit_v D.center D.scale
      D.scale_ne_zero D.planeMap hη hη1
  have hbandfix : ∀ y ∈ g '' (T '' (univ ×ˢ
      Icc (D.center + D.scale * η) c)), F y = y := by
    intro y hy
    rcases hy with ⟨z, ⟨⟨q, t⟩, ht, rfl⟩, rfl⟩
    apply hfix
    have hscale : D.scale < 0 := A.scale_neg
    have htIoo : t ∈ Ioo (D.center - δ) (c + δ) := by
      constructor
      · exact lt_of_lt_of_le hcut.1 ht.2.1
      · linarith [ht.2.2, hδ]
    rw [hheight q t htIoo]
    exact (div_le_iff_of_neg hscale).2 (by
      have heta : η ≤ (1 + η) / 2 := by linarith [hη1]
      nlinarith [ht.2.1, heta])
  refine ⟨δ, η, hδ, hη, hη1, T, hTs, hT, hTi, hTA, hheight, hcut,
    hcircles, F, hfix, ?_, hproj, ?_, hbandfix⟩
  · intro y hy
    have hH : Continuous (fun z : E3 =>
        (inner Real v z - D.center) / D.scale) :=
      ((innerSL Real v).continuous.sub continuous_const).div_const D.scale
    have hlt : (inner Real v y - D.center) / D.scale < (1 + η) / 2 := by
      have hle : (inner Real v y - D.center) / D.scale ≤ η :=
        (div_le_iff_of_neg A.scale_neg).2 (by linarith)
      linarith
    filter_upwards [hH.continuousAt.eventually (gt_mem_nhds hlt)] with z hz
    exact hfix z hz.le
  · have htrunc : F '' D.truncatedImage η =
        liftPlaneDiffeomorph D.unit_v (D.center + D.scale * η) D.scale
          D.scale_ne_zero D.planeMap '' boundedCylinderNorthernCap v := by
      simpa only [truncatedImage, D.range_eq, boundedCylinderNorthernCap] using himage
    rw [hdecomp, image_union, htrunc,
      image_congr hbandfix, image_id']

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

end

end M38Schoenflies
