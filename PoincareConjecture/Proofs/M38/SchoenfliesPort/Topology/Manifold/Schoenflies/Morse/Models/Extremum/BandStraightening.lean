import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.EndPreparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.BoundaryBand
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Extremum.AnnulusSlices
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.BandEndpoints







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real

private theorem prepared_circle_projection_range
    {v : E3} {f : S2 → E3}
    (P : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (e : OpenPartialHomeomorph E2 S2)
    (J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v)
    {c r ρ : Real} (hρ : 0 < ρ) (hr : 0 < r)
    (hcircle : ∀ q : E2, ‖q‖ = 1 →
      P (f (e (ρ • q))) = (r • J q : Hemisphere.Plane v) + c • v) :
    (Hemisphere.Plane v).orthogonalProjectionOnto ''
      (P '' (f '' (e '' sphere (0 : E2) ρ))) = sphere (0 : Hemisphere.Plane v) r := by
  rw [← image_unit_sphere_smul hρ]
  simp only [← range_comp, Function.comp_def]
  have hfun : (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
      (P (f (e (ρ • (q : E2)))))) = fun q : S1 => J (r • (q : E2)) := by
    funext q
    rw [hcircle q (mem_sphere_zero_iff_norm.mp q.property)]
    simp
  rw [hfun, show (fun q : S1 => J (r • (q : E2))) = J ∘ (fun q : S1 => r • (q : E2)) from rfl,
    range_comp, image_unit_sphere_smul hr, J.image_sphere, map_zero]

private theorem smoothEmbedding_postcompose_diffeomorph
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (P : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (P ∘ f) := by
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (P.contMDiff.comp hf.contMDiff) (P.injective.comp hf.isEmbedding.injective)
  intro p
  rw [mfderiv_comp p (P.contMDiff.mdifferentiable (by simp) _)
    (hf.contMDiff.mdifferentiable (by simp) p)]
  exact (P.mfderivToContinuousLinearEquiv (by simp) (f p)).injective.comp
    (injective_mfderiv_sphere_embedding hf p)

set_option maxHeartbeats 1000000 in




theorem exists_buffered_capped_minimum_disk_band_straightening_of_physical_annulus_cover
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) + ‖x‖ ^ 2)
    (hcover : ∃ R : Real, 0 < R ∧ inner Real v (f p) + R ^ 2 < b ∧
      closedBall (0 : E2) R ⊆ e.source ∧
      ∀ r ∈ Ioc (0 : Real) R,
        ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
          F.source = univ ×ˢ Ioo (inner Real v (f p) + r ^ 2 - δ) (b + δ) ∧
          ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
          ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
          (∀ q t, t ∈ Ioo (inner Real v (f p) + r ^ 2 - δ) (b + δ) →
            inner Real v (f (F (q, t))) = t) ∧
          range (fun q : S1 => F (q, inner Real v (f p) + r ^ 2)) =
            e '' sphere (0 : E2) r ∧
          F '' (univ ×ˢ Icc (inner Real v (f p) + r ^ 2) b) =
            (d '' closedBall 0 1) \ (e '' ball (0 : E2) r) ∧
          d '' closedBall 0 1 =
            e '' closedBall (0 : E2) r ∪
              F '' (univ ×ˢ Icc (inner Real v (f p) + r ^ 2) b))
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      f (T (q, t)) = (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1)
    {η : Real} (hη : 0 < η) :
    ∃ J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v, ∃ r ∈ Ioo (0 : Real) η,
      closedBall (0 : E2) r ⊆ e.source ∧
      let a := inner Real v (f p) + (7 * r / 8) ^ 2
      ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∃ δ : Real, 0 < δ ∧ ∀ (t : Real) (x : Hemisphere.Plane v), b - δ ≤ t →
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        (∀ x ∈ closedBall (0 : E2) (r / 2),
          D (f (e x)) = (J x : E3) + (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        (∀ x ∈ closedBall (0 : E2) (7 * r / 8),
          D (f (e x)) =
            ((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • J x : Hemisphere.Plane v) +
              (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        D '' (f '' ((d '' closedBall 0 1) \ (e '' ball (0 : E2) (7 * r / 8)))) =
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) r) ∧
        D '' (f '' (d '' closedBall 0 1)) =
          D '' (f '' (e '' closedBall (0 : E2) (7 * r / 8))) ∪
            (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
              (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
  let h : S2 → Real := fun q => inner Real v (f q)
  let c := h p
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  obtain ⟨hmin, hbounds, _, _⟩ :=
    height_bounds_on_disk_of_unique_critical hh d hds hp hpb hboundary hunique
  obtain ⟨R, hR, hRb, hRs, hcover⟩ := hcover
  obtain ⟨R₀, hR₀, _, _, _, hsublevels⟩ :=
    exists_exact_morse_sublevels_on_compact_disk hh d hds hp hpb hboundary hunique e he0 hep hform
  let η₀ := min η (min R (min R₀ (Real.sqrt ((b - c) / 4))))
  have hη₀ : 0 < η₀ := lt_min hη (lt_min hR (lt_min hR₀
    (Real.sqrt_pos.mpr (by dsimp [c]; linarith))))
  obtain ⟨J, r, hr, hrs, A₀, P, hPheight, hPupper, hPprofile, hPcenter, hPcylinder⟩ :=
    exists_minimum_preparation_with_profile hf hv p hmin e he0 hep he hei
      (fun _ => 1) (fun _ => Or.inr rfl)
      (by simpa only [one_mul, ← EuclideanSpace.real_norm_sq_eq] using hform) hη₀
  have hrη : r < η := hr.2.trans_le (min_le_left _ _)
  have hrR : r ≤ R := hr.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrR₀ : r ≤ R₀ := hr.2.le.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hrroot : r < Real.sqrt ((b - c) / 4) := hr.2.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrsmall : r ^ 2 < (b - c) / 4 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (b - c) / 4 by dsimp [c]; linarith),
      Real.sqrt_nonneg ((b - c) / 4), hr.1]
  let ρ := 7 * r / 8
  let a := c + ρ ^ 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith [hr.1]
  have hρr : ρ ≤ r := by dsimp [ρ]; linarith [hr.1]
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hFheight, _, hFband, hKcover⟩ :=
    hcover ρ ⟨hρ, hρr.trans hrR⟩
  obtain ⟨hclosedρ, hopenρ, _⟩ := hsublevels ρ ⟨hρ, hρr.trans hrR₀⟩
  have hab : a < b := by dsimp [a, ρ]; dsimp [c] at hrsmall; nlinarith [hrsmall]
  have hbandfull : F '' (univ ×ˢ Icc a b) =
      (d '' closedBall 0 1) ∩ h ⁻¹' Icc a b := by
    rw [hFband, hopenρ]
    ext x
    constructor
    · rintro ⟨hx, hxnot⟩
      exact ⟨hx, le_of_not_gt (fun hlt => hxnot ⟨hx, hlt⟩), (hbounds x hx).2⟩
    · rintro ⟨hx, hxa, hxb⟩
      exact ⟨hx, fun hlt => (not_lt_of_ge hxa) hlt.2⟩
  have hslice (t : Real) (ht : t ∈ Icc a b) :
      range (fun q : S1 => F (q, t)) = (d '' closedBall 0 1) ∩ h ⁻¹' {t} := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      have hx : F (q, t) ∈ F '' (univ ×ˢ Icc a b) :=
        mem_image_of_mem F ⟨mem_univ _, ht⟩
      rw [hbandfull] at hx
      exact ⟨hx.1, hFheight q t ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    · rintro ⟨hxK, hxt⟩
      have hxband : x ∈ (d '' closedBall 0 1) ∩ h ⁻¹' Icc a b := by
        refine ⟨hxK, ?_⟩
        change h x ∈ Icc a b
        rw [show h x = t from hxt]
        exact ht
      rw [← hbandfull] at hxband
      obtain ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩ := hxband
      have hst : s = t := (hFheight q s
        ⟨by linarith [hs.1], by linarith [hs.2]⟩).symm.trans hxt
      exact ⟨q, by rw [hst]⟩
  have hTh (q : S1) (t : Real) (ht : t ∈ Ioo (-ε) ε) : h (T (q, t)) = b + t := by
    change inner Real v (f (T (q, t))) = _
    rw [hTcylinder q t ht]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (γ q).property]
  obtain ⟨δtop, hδtop, hδtopε, htop⟩ :=
    exists_boundary_band_cover_of_unique_critical_disk hh d hds hp hpb hboundary hunique
      hε T hTs hTh hTc hTneg
  let w := min (δtop / 2) (min (r ^ 2 / 128) ((b - c) / 16))
  have hw : 0 < w := lt_min (half_pos hδtop)
    (lt_min (div_pos (sq_pos_of_pos hr.1) (by norm_num)) (by dsimp [c]; linarith))
  have hwtop : w ≤ δtop / 2 := min_le_left _ _
  have hwr : w ≤ r ^ 2 / 128 := (min_le_right _ _).trans (min_le_left _ _)
  have hwgap : w ≤ (b - c) / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hsep : a + w < b - w := by dsimp [a, ρ]; nlinarith [hrsmall, sq_pos_of_pos hr.1]
  let C : Real → Set (Hemisphere.Plane v) := fun t =>
    range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (P (f (F (q, t)))))
  have hCimage (t : Real) : C t = (Hemisphere.Plane v).orthogonalProjectionOnto ''
      (P '' (f '' range (fun q : S1 => F (q, t)))) := by
    simp only [← range_comp, Function.comp_def]
    rfl
  have hCleft (t : Real) (ht : t ∈ Icc a (a + w)) : C t = sphere 0 r := by
    let s := Real.sqrt (t - c)
    have hsc : 0 < t - c := by dsimp [a] at ht; nlinarith [sq_pos_of_pos hρ, ht.1]
    have hs : 0 < s := Real.sqrt_pos.mpr hsc
    have hssq : s ^ 2 = t - c := Real.sq_sqrt hsc.le
    have hslo : 3 * r / 4 ≤ s := by dsimp [a, ρ] at ht; nlinarith [ht.1, hr.1]
    have hshi : s ≤ r := by dsimp [a, ρ] at ht; nlinarith [ht.2, hr.1]
    obtain ⟨_, _, hcircle⟩ := hsublevels s ⟨hs, hshi.trans hrR₀⟩
    have hlevel : (d '' closedBall 0 1) ∩ h ⁻¹' {t} = e '' sphere (0 : E2) s := by
      rw [hcircle, show h p + s ^ 2 = t by dsimp [c] at hssq; linarith]
    rw [hCimage, hslice t ⟨ht.1, by linarith [ht.2]⟩, hlevel]
    have htformula : inner Real v (f p) + s ^ 2 = t := by
      change c + s ^ 2 = t
      linarith
    exact prepared_circle_projection_range P e J hs hr.1
      (fun q hq => by simpa only [htformula] using hPcylinder q s hq ⟨hslo, hshi⟩)
  have hCright (t : Real) (ht : t ∈ Icc (b - w) b) : C t = range (fun q => A₀ (γ q)) := by
    have httop : t - b ∈ Icc (-δtop) 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htε : t - b ∈ Ioo (-ε) ε := ⟨by linarith [httop.1], by linarith [httop.2]⟩
    have htupper : c + 3 * r ^ 2 / 2 ≤ t := by nlinarith [hrsmall, ht.1]
    have hlevel : (d '' closedBall 0 1) ∩ h ⁻¹' {t} =
        range (fun q : S1 => T (q, t - b)) := by
      rw [← htop (t - b) httop, add_sub_cancel]
    rw [hCimage, hslice t ⟨by linarith [ht.1], ht.2⟩, hlevel]
    simp only [← range_comp, Function.comp_def]
    congr 1
    funext q
    rw [hTcylinder q (t - b) htε, add_sub_cancel, hPupper t (γ q) htupper]
    simp
  have hfP := smoothEmbedding_postcompose_diffeomorph hf P
  obtain ⟨Q, _, B, hBheight, hBlow, hBupper, _, hBband⟩ :=
    exists_actual_band_flattening_with_constant_ends hfP hv hδ hw hsep F hFs hF hFi
      (fun q t ht => (hPheight _).trans (hFheight q t ht))
      (fun t ht => (hCleft t ht).trans (hCleft a ⟨le_rfl, by linarith⟩).symm)
      (fun t ht => (hCright t ht).trans (hCright b ⟨by linarith, le_rfl⟩).symm)
  let D := P.trans B
  let A := A₀.trans Q
  have hDband : D '' (f '' ((d '' closedBall 0 1) \ (e '' ball (0 : E2) ρ))) =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
    rw [← hFband]
    change (B ∘ P) '' _ = _
    rw [image_comp, ← image_comp P f, hBband]
    congr 2
    exact hCleft a ⟨le_rfl, by linarith⟩
  refine ⟨J, r, ⟨hr.1, hrη⟩, hrs, A, D, ?_, ?_, ?_, ?_, hDband, ?_⟩
  · intro y
    exact (hBheight (P y)).trans (hPheight y)
  · refine ⟨w / 4, by linarith, ?_⟩
    intro t x ht
    change B (P (t • v + (x : E3))) = _
    rw [hPupper t x (by change c + 3 * r ^ 2 / 2 ≤ t; nlinarith [hrsmall]),
      hBupper t (A₀ x) (by linarith)]
    rfl
  · intro x hx
    change B (P (f (e x))) = _
    rw [hBlow]
    · exact hPcenter x hx
    · rw [hPheight]
      have hxs := hrs (closedBall_subset_closedBall (by linarith [hr.1] : r / 2 ≤ r) hx)
      rw [hform x hxs]
      have hxnorm := mem_closedBall_zero_iff.mp hx
      change c + ‖x‖ ^ 2 ≤ a + w / 4
      dsimp [a, ρ]
      nlinarith [norm_nonneg x]
  · intro x hx
    have hxr : x ∈ closedBall (0 : E2) r := closedBall_subset_closedBall hρr hx
    change B (P (f (e x))) = _
    rw [hBlow]
    · exact hPprofile x hxr
    · rw [hPheight, hform x (hrs hxr)]
      have hxnorm := mem_closedBall_zero_iff.mp hx
      change c + ‖x‖ ^ 2 ≤ a + w / 4
      dsimp [a, ρ] at *
      nlinarith [norm_nonneg x]
  · rw [hKcover, image_union, image_union]
    congr 1
    rw [hFband]
    exact hDband


set_option maxHeartbeats 1000000 in


theorem exists_capped_minimum_disk_band_straightening_of_physical_annulus_cover
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) + ‖x‖ ^ 2)
    (hcover : ∃ R : Real, 0 < R ∧ inner Real v (f p) + R ^ 2 < b ∧
      closedBall (0 : E2) R ⊆ e.source ∧
      ∀ r ∈ Ioc (0 : Real) R,
        ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
          F.source = univ ×ˢ Ioo (inner Real v (f p) + r ^ 2 - δ) (b + δ) ∧
          ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
          ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
          (∀ q t, t ∈ Ioo (inner Real v (f p) + r ^ 2 - δ) (b + δ) →
            inner Real v (f (F (q, t))) = t) ∧
          range (fun q : S1 => F (q, inner Real v (f p) + r ^ 2)) =
            e '' sphere (0 : E2) r ∧
          F '' (univ ×ˢ Icc (inner Real v (f p) + r ^ 2) b) =
            (d '' closedBall 0 1) \ (e '' ball (0 : E2) r) ∧
          d '' closedBall 0 1 =
            e '' closedBall (0 : E2) r ∪
              F '' (univ ×ˢ Icc (inner Real v (f p) + r ^ 2) b))
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      f (T (q, t)) = (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1)
    {η : Real} (hη : 0 < η) :
    ∃ J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v, ∃ r ∈ Ioo (0 : Real) η,
      closedBall (0 : E2) r ⊆ e.source ∧
      let a := inner Real v (f p) + (7 * r / 8) ^ 2
      ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∀ (t : Real) (x : Hemisphere.Plane v), b ≤ t →
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        (∀ x ∈ closedBall (0 : E2) (r / 2),
          D (f (e x)) = (J x : E3) + (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        (∀ x ∈ closedBall (0 : E2) (7 * r / 8),
          D (f (e x)) =
            ((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • J x : Hemisphere.Plane v) +
              (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        D '' (f '' ((d '' closedBall 0 1) \ (e '' ball (0 : E2) (7 * r / 8)))) =
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) r) ∧
        D '' (f '' (d '' closedBall 0 1)) =
          D '' (f '' (e '' closedBall (0 : E2) (7 * r / 8))) ∪
            (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
              (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
  obtain ⟨J, r, hr, hrs, A, D, hh, ⟨δ, hδ, hu⟩, hc, hp, hb, hw⟩ :=
    exists_buffered_capped_minimum_disk_band_straightening_of_physical_annulus_cover
      hf hv d hds hp hpb hboundary hunique e he0 hep he hei hform hcover
      hε T hTs γ hTcylinder hTc hTneg hη
  exact ⟨J, r, hr, hrs, A, D, hh, fun t x ht => hu t x (by linarith),
    hc, hp, hb, hw⟩


set_option maxHeartbeats 1000000 in



theorem exists_capped_minimum_disk_band_straightening
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real}
    (hpb : inner Real v (f p) < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (habove : ∀ x ∉ d '' closedBall 0 1, b < inner Real v (f x))
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
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1)
    {η : Real} (hη : 0 < η) :
    ∃ J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v, ∃ r ∈ Ioo (0 : Real) η,
      closedBall (0 : E2) r ⊆ e.source ∧
      let a := inner Real v (f p) + (7 * r / 8) ^ 2
      ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∀ (t : Real) (x : Hemisphere.Plane v), b ≤ t →
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        (∀ x ∈ closedBall (0 : E2) (r / 2),
          D (f (e x)) = (J x : E3) + (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        (∀ x ∈ closedBall (0 : E2) (7 * r / 8),
          D (f (e x)) =
            ((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • J x : Hemisphere.Plane v) +
              (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        D '' (f '' ((d '' closedBall 0 1) \ (e '' ball (0 : E2) (7 * r / 8)))) =
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) r) ∧
        D '' (f '' (d '' closedBall 0 1)) =
          D '' (f '' (e '' closedBall (0 : E2) (7 * r / 8))) ∪
            (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
              (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (f q)) :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  exact exists_capped_minimum_disk_band_straightening_of_physical_annulus_cover
    hf hv d hds hp hpb hboundary hunique e he0 hep he hei hform
    (exists_morse_disk_and_annulus_cover hh d hds hp hpb hboundary hunique
      habove e he0 hep hform)
    hε T hTs γ hTcylinder hTc hTneg hη

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
