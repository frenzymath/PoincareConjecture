import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.TerminalNormalization
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.BandEndpoints
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Relative.HalfSpace







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1




theorem exists_supported_cylindrical_lower_terminal_end_normalization
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) (hDb : D.center < b)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {w : Real} (hw : 0 < w)
    (hconstant : ∀ t ∈ Icc (b - w) b,
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (A.chart (q, t)))) =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (A.chart (q, b))))) :
    ∃ d u : Real, d < D.center ∧ 0 < u ∧ u < w ∧ d + u < b - u ∧
      ∃ Q : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ S : Set E3, IsCompact S ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (D.planeMap.trans Q.symm) '' sphere (0 : Hemisphere.Plane v) 1 =
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (g (A.chart (q, b)))) ∧
        (∀ y ∉ S, R y = y) ∧
        (∀ y, b - u / 4 ≤ inner Real v y → R y = y) ∧
        R '' (g '' A.cappedRegion b) =
          (liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero
            (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) ∪
          (fun x : Real × Hemisphere.Plane v => x.1 • v + (x.2 : E3)) ''
            (Icc d b ×ˢ range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
              (g (A.chart (q, b))))) := by
  obtain ⟨d, δ, hdD, hδ, T, L, hTs, hT, hTi, hTA, hheight,
    hcircles, hLfix, _, hLend⟩ :=
    exists_lower_terminal_end_normalization A hg haD hDb hgerm
  let u := min w (min (D.center - d) ((b - d) / 4)) / 2
  have hu : 0 < u := half_pos (lt_min hw
    (lt_min (sub_pos.mpr hdD) (div_pos (sub_pos.mpr (hdD.trans hDb)) (by norm_num))))
  have huw : u < w := by
    dsimp [u]
    linarith [min_le_left w (min (D.center - d) ((b - d) / 4))]
  have huD : u < D.center - d := by
    have hm := (min_le_right w (min (D.center - d) ((b - d) / 4))).trans
      (min_le_left _ _)
    dsimp [u]
    linarith
  have husep : d + u < b - u := by
    have hm := (min_le_right w (min (D.center - d) ((b - d) / 4))).trans
      (min_le_right _ _)
    dsimp [u]
    linarith
  have hleft (t : Real) (ht : t ∈ Icc d (d + u)) :
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (T (q, t)))) = D.planeMap '' sphere (0 : Hemisphere.Plane v) 1 :=
    hcircles t ⟨ht.1, by linarith [ht.2]⟩
  have hright (t : Real) (ht : t ∈ Icc (b - u) b) :
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (T (q, t)))) =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (T (q, b)))) := by
    simpa only [hTA] using hconstant t ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨Q, hQ, N, _, hNlow, hNupper, _, hNband⟩ :=
    exists_actual_band_flattening_with_constant_ends hg D.unit_v hδ hu husep
      T hTs hT hTi hheight
      (fun t ht => (hleft t ht).trans (hleft d ⟨le_rfl, by linarith⟩).symm) hright
  have hQcircle : Q '' range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
      (g (A.chart (q, b)))) = D.planeMap '' sphere (0 : Hemisphere.Plane v) 1 := by
    simpa only [hTA] using hQ.trans (hleft d ⟨le_rfl, by linarith⟩)
  have hQinv : Q.symm '' (D.planeMap '' sphere (0 : Hemisphere.Plane v) 1) =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (A.chart (q, b)))) := by
    rw [← hQcircle, image_image]
    simp only [Q.symm_apply_apply, image_id']
  let J := liftPlaneDiffeomorph D.unit_v 0 1 one_ne_zero Q.symm
  have hJplane (t : Real) (x : Hemisphere.Plane v) :
      J (t • v + (x : E3)) = t • v + (Q.symm x : E3) := by
    have hcoords := (heightCoordinates D.unit_v).symm_apply_apply (t, x)
    have ht : inner Real v (t • v + (x : E3)) = t := congrArg Prod.fst hcoords
    have hx : (Hemisphere.Plane v).orthogonalProjectionOnto (t • v + (x : E3)) = x :=
      congrArg Prod.snd hcoords
    simp only [J, liftPlaneDiffeomorph_apply, ht, hx, one_mul, zero_add]
  let lower := liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero D.planeMap ''
    boundedCylinderNorthernCap v
  have hNlower : N '' lower = lower := by
    calc
      _ = id '' lower := by
        apply image_congr
        rintro y ⟨z, hz, rfl⟩
        apply hNlow
        rw [inner_liftPlaneDiffeomorph]
        have hz0 := height_nonneg_of_mem_boundedCylinderNorthernCap hz
        nlinarith [A.scale_neg]
      _ = _ := image_id _
  have hJlower : J '' lower =
      liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero
        (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v := by
    rw [show lower = _ from rfl, ← image_comp]
    apply image_congr
    intro z _
    change J (liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero D.planeMap z) = _
    rw [liftPlaneDiffeomorph_apply D.unit_v d D.scale D.scale_ne_zero D.planeMap,
      hJplane, liftPlaneDiffeomorph_apply]
    rfl
  have hJband : J '' (N '' (g '' (T '' (univ ×ˢ Icc d b)))) =
      (fun x : Real × Hemisphere.Plane v => x.1 • v + (x.2 : E3)) ''
        (Icc d b ×ˢ range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
          (g (A.chart (q, b))))) := by
    rw [hNband, hleft d ⟨le_rfl, by linarith⟩, ← hQinv, image_image]
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      exact ⟨(t, Q.symm x), ⟨ht, mem_image_of_mem Q.symm hx⟩, (hJplane t x).symm⟩
    · rintro ⟨⟨t, _⟩, ⟨ht, x, hx, rfl⟩, rfl⟩
      exact ⟨(t, x), ⟨ht, hx⟩, hJplane t x⟩
  let F := (L.trans N).trans J
  have hFfix (y : E3) (hy : b - u / 4 ≤ inner Real v y) : F y = y := by
    change J (N (L y)) = y
    rw [hLfix y (by linarith)]
    have hcoords := (heightCoordinates D.unit_v).apply_symm_apply y
    change (inner Real v y) • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y at hcoords
    conv_lhs => rw [← hcoords]
    rw [hNupper _ _ hy, hJplane, Q.symm_apply_apply]
    exact hcoords
  have hFend : F '' (g '' A.cappedRegion b) =
      (liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero
        (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) ∪
      (fun x : Real × Hemisphere.Plane v => x.1 • v + (x.2 : E3)) ''
        (Icc d b ×ˢ range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
          (g (A.chart (q, b))))) := by
    simp only [F, Diffeomorph.coe_trans, image_comp]
    rw [hLend, image_union, image_union, hNlower, hJlower, hJband]
  have hK : IsCompact (g '' A.cappedRegion b) :=
    (A.isCompact_cappedRegion haD le_rfl).image hg.contMDiff.continuous
  have hv : (innerSL Real v) v = 1 := by
    simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq, D.unit_v, one_pow]
  obtain ⟨S, hS, R, hsupport, hfixed, hagree⟩ :=
    exists_supported_agreement_of_fixed_halfspace (innerSL Real v) v hv
      (b - u / 4) F hFfix hK
  refine ⟨d, u, hdD, hu, huw, husep, Q, S, hS, R, ?_, hsupport, hfixed,
    (image_congr hagree).trans hFend⟩
  change (Q.symm ∘ D.planeMap) '' sphere (0 : Hemisphere.Plane v) 1 = _
  rw [image_comp]
  exact hQinv

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
