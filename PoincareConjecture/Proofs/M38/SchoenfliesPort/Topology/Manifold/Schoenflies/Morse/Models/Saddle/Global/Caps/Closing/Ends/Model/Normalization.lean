import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Straightening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.QuadraticScaling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Relative.HalfSpace







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

open Set Metric Function
open scoped Manifold ContDiff Topology Pointwise

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1




theorem exists_buffered_relative_component_minimum_disk_normalization
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
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
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      f (T (q, t)) = (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1) :
    ∃ l s : Real, ∃ hs : s < 0, l < b ∧
      ∃ B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v),
      ∃ K : Set E3, IsCompact K ∧
      ∃ N : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : Hemisphere.Plane v) 1 = range γ ∧
        (∀ y ∉ K, N y = y) ∧
        (∃ δ : Real, 0 < δ ∧ ∀ y, b - δ ≤ inner Real v y → N y = y) ∧
        N '' (f '' (d '' closedBall 0 1)) =
          (liftPlaneDiffeomorph hv l s hs.ne B '' boundedCylinderNorthernCap v) ∪
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc l b ×ˢ range γ) := by
  obtain ⟨r, hr, hrb, A, D, hDheight, ⟨δ, hδ, hDupper⟩, hwhole⟩ :=
    exists_buffered_component_minimum_disk_straightening hf hv d hds hp hpb hboundary hunique
      seed hcomponent hregular e he0 hep he hei hform hε T hTs γ hTcylinder hTc hTneg
      (show (0 : Real) < 1 by norm_num)
  let c := inner Real v (f p)
  let l := c + 2 * r ^ 2
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr.1
  have hab : c + (7 * r / 8) ^ 2 < b := by dsimp [c]; nlinarith
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (f q)) :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  have hstrict := (height_bounds_on_disk_of_unique_critical hh d hds hp hpb hboundary hunique).2.2.2
  have htop := closed_disk_top_level_eq_boundary d (fun q => inner Real v (f q)) b hboundary hstrict
  have hboundaryimage := image_minimum_disk_top_boundary hv hr.1 hab f (d '' closedBall 0 1)
    (d '' sphere (0 : E2) 1) htop D hDheight hwhole
  let π := (Hemisphere.Plane v).orthogonalProjectionOnto
  have hprojfun : (fun q : S1 => π (D (f (T (q, 0))))) = fun q : S1 => A (γ q) := by
    funext q
    rw [hTcylinder q 0 ⟨by linarith, hε⟩, add_zero, hDupper b (γ q) (by linarith)]
    exact congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (b, A (γ q)))
  have hprojleft : π '' (D '' (f '' (d '' sphere (0 : E2) 1))) = range (fun q => A (γ q)) := by
    rw [← hTc]
    simp only [← range_comp, Function.comp_def]
    exact congrArg Set.range hprojfun
  have hprojright : π '' ((fun q : Hemisphere.Plane v => b • v + (q : E3)) ''
      sphere (0 : Hemisphere.Plane v) r) = sphere (0 : Hemisphere.Plane v) r := by
    rw [image_image]
    have heq : (fun q : Hemisphere.Plane v => π (b • v + (q : E3))) = id := by
      funext q
      exact congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (b, q))
    rw [heq, image_id]
  have hAcircle : A '' range γ = sphere (0 : Hemisphere.Plane v) r := by
    rw [← range_comp]
    exact hprojleft.symm.trans
      ((congrArg (fun W : Set E3 => π '' W) hboundaryimage).trans hprojright)
  have hAinv : A.symm '' sphere (0 : Hemisphere.Plane v) r = range γ := by
    rw [← hAcircle, image_image]
    simp only [A.symm_apply_apply, image_id']
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro hv0; simp [hv0] at hv)).repr
  obtain ⟨C, hC, η, hη, P, hPfix, _, hPimage⟩ :=
    exists_relative_scaled_quadratic_lower_transport hv J c hr.1 hrb
  let B := C.trans A.symm
  have hCsphere : C '' sphere (0 : Hemisphere.Plane v) 1 = sphere 0 r := by
    rw [show (C : Hemisphere.Plane v → Hemisphere.Plane v) = (fun x => r • x) from funext hC]
    change r • sphere (0 : Hemisphere.Plane v) 1 = _
    rw [smul_sphere' hr.1.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr.1, mul_one]
  have hBcircle : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ := by
    change (A.symm ∘ C) '' sphere (0 : Hemisphere.Plane v) 1 = _
    rw [image_comp, hCsphere, hAinv]
  let L := liftPlaneDiffeomorph hv 0 1 one_ne_zero A.symm
  have hLplane (t : Real) (x : Hemisphere.Plane v) :
      L (t • v + (x : E3)) = t • v + (A.symm x : E3) := by
    have hcoords := (heightCoordinates hv).symm_apply_apply (t, x)
    have ht : inner Real v (t • v + (x : E3)) = t := congrArg Prod.fst hcoords
    have hx : (Hemisphere.Plane v).orthogonalProjectionOnto (t • v + (x : E3)) = x :=
      congrArg Prod.snd hcoords
    simp only [L, liftPlaneDiffeomorph_apply, ht, hx, one_mul, zero_add]
  have hLcap : L '' (liftPlaneDiffeomorph hv l (-(r ^ 2)) (neg_ne_zero.mpr hr2.ne') C ''
      boundedCylinderNorthernCap v) =
      liftPlaneDiffeomorph hv l (-(r ^ 2)) (neg_ne_zero.mpr hr2.ne') B ''
        boundedCylinderNorthernCap v := by
    rw [← image_comp]
    apply image_congr
    intro z _
    change L (liftPlaneDiffeomorph hv l (-(r ^ 2)) (neg_ne_zero.mpr hr2.ne') C z) = _
    rw [liftPlaneDiffeomorph_apply hv l (-(r ^ 2)) (neg_ne_zero.mpr hr2.ne') C,
      hLplane, liftPlaneDiffeomorph_apply]
    rfl
  have hLcylinder : L '' ((fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
      (Icc l b ×ˢ sphere (0 : Hemisphere.Plane v) r)) =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) '' (Icc l b ×ˢ range γ) := by
    rw [← hAinv, image_image]
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      exact ⟨(t, A.symm x), ⟨ht, mem_image_of_mem A.symm hx⟩, (hLplane t x).symm⟩
    · rintro ⟨⟨t, _⟩, ⟨ht, x, hx, rfl⟩, rfl⟩
      exact ⟨(t, x), ⟨ht, hx⟩, hLplane t x⟩
  let H := (D.trans P).trans L
  let w := min δ ((b - l) / 2)
  have hw : 0 < w := lt_min hδ (by dsimp [l, c]; linarith)
  have hwδ : w ≤ δ := min_le_left _ _
  have hwl : w ≤ (b - l) / 2 := min_le_right _ _
  have hHfix (y : E3) (hy : b - w ≤ inner Real v y) : H y = y := by
    change L (P (D y)) = y
    rw [hPfix _ (by rw [hDheight]; dsimp [l, c] at hwl; dsimp [c]; linarith)]
    have hcoords := (heightCoordinates hv).apply_symm_apply y
    change (inner Real v y) • v + ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y
      at hcoords
    conv_lhs => rw [← hcoords]
    rw [hDupper _ _ (by linarith), hLplane, A.symm_apply_apply]
    exact hcoords
  have hHimage : H '' (f '' (d '' closedBall 0 1)) =
      (liftPlaneDiffeomorph hv l (-(r ^ 2)) (neg_ne_zero.mpr hr2.ne') B ''
        boundedCylinderNorthernCap v) ∪
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) '' (Icc l b ×ˢ range γ) := by
    simp only [H, Diffeomorph.coe_trans, image_comp]
    rw [hwhole, hPimage, image_union, hLcap, hLcylinder]
  have hcompact : IsCompact (f '' (d '' closedBall 0 1)) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn
      (d.continuousOn.mono hds)).image hf.contMDiff.continuous
  have hunit : (innerSL Real v) v = 1 := by
    simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq, hv, one_pow]
  obtain ⟨K, hK, N, hsupport, hfixed, hagree⟩ :=
    exists_supported_agreement_of_fixed_halfspace (innerSL Real v) v hunit (b - w) H hHfix hcompact
  exact ⟨l, -(r ^ 2), neg_neg_of_pos hr2, hrb, B, K, hK, N, hBcircle,
    hsupport, ⟨w, hw, hfixed⟩, (image_congr hagree).trans hHimage⟩


theorem exists_relative_component_minimum_disk_normalization
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
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
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      f (T (q, t)) = (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1) :
    ∃ l s : Real, ∃ hs : s < 0, l < b ∧
      ∃ B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v),
      ∃ K : Set E3, IsCompact K ∧
      ∃ N : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : Hemisphere.Plane v) 1 = range γ ∧
        (∀ y ∉ K, N y = y) ∧
        (∀ y, b ≤ inner Real v y → N y = y) ∧
        N '' (f '' (d '' closedBall 0 1)) =
          (liftPlaneDiffeomorph hv l s hs.ne B '' boundedCylinderNorthernCap v) ∪
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc l b ×ˢ range γ) := by
  obtain ⟨l, s, hs, hl, B, K, hK, N, hB, hN, ⟨δ, hδ, hu⟩, hi⟩ :=
    exists_buffered_relative_component_minimum_disk_normalization hf hv d hds hp hpb
      hboundary hunique seed hcomponent hregular e he0 hep he hei hform hε T hTs γ
      hTcylinder hTc hTneg
  exact ⟨l, s, hs, hl, B, K, hK, N, hB, hN, fun y hy => hu y (by linarith), hi⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
