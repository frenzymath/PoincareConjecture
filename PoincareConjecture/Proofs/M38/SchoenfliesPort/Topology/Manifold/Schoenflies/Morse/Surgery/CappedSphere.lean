import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.InwardDisk
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Clock
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.Splicing
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.ParametrizedCap
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Clearance

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem exists_capped_sphere_of_cylindrical_tube_with_disk_and_range_for_small_scale
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {ε : Real} (hε : 0 < ε)
    {τ : Real} (hτ : 0 < τ)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 -> Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (hcylinder : ∀ p t, t ∈ Ioo (-ε) ε ->
      f (T (p, t)) = (c + t) • v + (γ p : E3))
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hintersection :
      ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => T (p, 0)))
    (e : OpenPartialHomeomorph E2 S2)
    (hesource : closedBall 0 1 ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hecenter : range (fun p : S1 => T (p, 0)) = e '' sphere (0 : E2) 1)
    (henegative : ∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ e '' ball 0 1) :
    ∃ δ : Real, 0 < δ ∧ ∀ s : Real, -δ < s → ∀ hs : s < 0,
    ∃ d : OpenPartialHomeomorph E2 S2,
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      closedBall 0 1 ⊆ d.source ∧
      d '' closedBall 0 1 = e '' closedBall 0 1 ∧
      d '' ball 0 1 = e '' ball 0 1 ∧
      range (fun p : S1 => T (p, 0)) = d '' sphere (0 : E2) 1 ∧
      (∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ d '' ball 0 1) ∧
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
        ∃ g : E2 -> E3,
          ContDiff Real ∞ g ∧ Injective g ∧
          (∀ x, Injective (fderiv Real g x)) ∧
          (∀ p : S1, g p = f (d p) ∧ g p = c • v + (γ (q p) : E3)) ∧
          (∀ x, ‖x‖ < 1 -> inner Real v (g x) < c) ∧
          (∀ x, |inner Real v (g x) - c| < τ) ∧
          (∃ η : Real, 0 < η ∧ η < 1 ∧
            ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η ->
              ρ • (p : E2) ∈ d.source ∧
              d (ρ • (p : E2)) = T (q p, s * ((1 - ρ ^ 2) / (2 * ρ))) ∧
              g (ρ • (p : E2)) = f (d (ρ • (p : E2)))) ∧
          Disjoint (g '' ball 0 1) (f '' (d '' ball 0 1)ᶜ) ∧
          g '' closedBall (0 : E2) 1 =
            Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs.ne A ''
              ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
                {p : S2 | 0 ≤ inner Real v (p : E3)}) ∧
          ∃ f' : S2 -> E3,
            _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f' ∧
            (∀ x ∈ closedBall 0 1, f' (d x) = g x) ∧
            (∀ y ∉ d '' ball 0 1, f' y = f y) ∧
            range f' = g '' closedBall 0 1 ∪ f '' (d '' ball 0 1)ᶜ := by
  have hheight (p : S1) (t : Real) (ht : t ∈ Ioo (-ε) ε) :
      inner Real v (f (T (p, t))) = c + t := by
    rw [hcylinder p t ht]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (γ p).property]
  let D := (fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1
  have hD : IsCompact D := (isCompact_closedBall _ _).image
    (continuous_const.add (continuous_subtype_val.comp A.contMDiff.continuous))
  have hplane : D ⊆ {y : E3 | inner Real v y = c} := by
    rintro y ⟨x, _, rfl⟩
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A x).property]
  obtain ⟨δ, hδ, _, W, _, hDW, hclear⟩ := exists_regular_tube_disk_clearance
    hf.contMDiff.continuous hf.isEmbedding.injective hv (r := ε / 2)
    (by positivity) (by linarith) T hsource rfl hD hplane hintersection
  refine ⟨min δ τ / 2, half_pos (lt_min hδ hτ), ?_⟩
  intro s hsδ hs
  have hsbound : 2 * |s| < min δ τ := by
    rw [abs_of_neg hs]
    linarith
  obtain ⟨d, hd, hdi, hdsource, hdclosed, hdball, hdfix, q, a, ha, ha1, hdclock⟩ :=
    exists_disk_chart_matching_cap_clock e he hei hesource hε T hT hTi hsource
      hecenter henegative hs
  have hdcenter : range (fun p : S1 => T (p, 0)) = d '' sphere (0 : E2) 1 := by
    rw [hecenter]
    apply image_congr
    intro x hx
    exact (hdfix ⟨x, hx⟩).symm
  have hdnegative (p : S1) (t : Real) (ht : t ∈ Ioo (-ε) 0) :
      T (p, t) ∈ d '' ball 0 1 := hdball.symm ▸ henegative p t ht
  have hγq : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞
      (γ ∘ q) := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (hγ.contMDiff.comp q.contMDiff) (hγ.isEmbedding.injective.comp q.injective)
    intro p
    rw [mfderiv_comp p (hγ.contMDiff.mdifferentiable (by simp) (q p))
      (q.contMDiff.mdifferentiable (by simp) p)]
    exact ((hγ.isImmersion.isImmersionAt (q p)).injective_mfderiv_modelWithCornersSelf
      (by simp)).comp (q.mfderivToContinuousLinearEquiv (by simp) p).injective
  have hboundaryq : A '' sphere (0 : Hemisphere.Plane v) 1 = range (γ ∘ q) := by
    rw [hboundary]
    convert! (q.surjective.range_comp γ).symm using 1
  obtain ⟨g, hg, hginj, hgder, hgboundary, hgheight, ⟨b, hb, hb1, hgclock⟩,
    hgbounds, hgrange⟩ :=
    exists_parametrized_cylindrical_cap_with_range hv (γ ∘ q) hγq A hboundaryq c s hs.ne
  have hgnegative (x : E2) (hx : ‖x‖ < 1) : inner Real v (g x) < c := by
    rcases div_pos_iff.mp (hgheight x hx) with h | h
    · exact (not_lt_of_ge hs.le h.2).elim
    · linarith [h.1]
  have hgwidth (x : E2) : |inner Real v (g x) - c| < τ := by
    exact (hgbounds x).2.trans_lt (hsbound.trans_le (min_le_right δ τ))
  have hdisjoint : Disjoint (g '' ball 0 1) (f '' (d '' ball 0 1)ᶜ) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨p, hp, hpeq⟩
    let t := inner Real v (g x) - c
    have htneg : t < 0 := sub_neg.mpr (hgnegative x (mem_ball_zero_iff.mp hx))
    have ht : t ∈ Icc (-δ) δ := by
      have hbnd' : |t| ≤ δ :=
        (hgbounds x).2.trans (hsbound.le.trans (min_le_left δ τ))
      exact abs_le.mp hbnd'
    obtain ⟨z, hz, hproj⟩ := (hgbounds x).1
    let y : E3 := c • v + (A z : E3)
    have hyD : y ∈ D := ⟨z, hz, rfl⟩
    have hdecomp : g x = y + t • v := by
      have h := (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply (g x)
      change inner Real v (g x) • v +
        ((Hemisphere.Plane v).orthogonalProjectionOnto (g x) : E3) = g x at h
      rw [← hproj] at h
      rw [← h]
      dsimp [y, t]
      module
    obtain ⟨w, hw, hwy⟩ := hDW hyD
    have hcap : g x ∈ ((fun z : {y : E3 | inner Real v y = c} × Real =>
        (z.1 : E3) + z.2 • v) '' (W ×ˢ Icc (-δ) δ)) ∩ range f := by
      refine ⟨⟨(w, t), ⟨hw, ht⟩, ?_⟩, ⟨p, hpeq⟩⟩
      exact (congrArg (fun a : E3 => a + t • v) hwy).trans hdecomp.symm
    obtain ⟨p', ⟨⟨q', u⟩, hu, hTp'⟩, hfp'⟩ := hclear hcap
    have huε : u ∈ Ioo (-ε) ε := ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩
    have hut : u = t := by
      have heq := congrArg (inner Real v) hfp'
      rw [← hTp', hheight q' u huε] at heq
      dsimp [t]
      linarith
    apply hp
    have hpp' : p' = p := hf.isEmbedding.injective (hfp'.trans hpeq.symm)
    rw [← hpp', ← hTp']
    exact hdnegative q' u ⟨huε.1, hut ▸ htneg⟩
  let η := min a b
  have hη : 0 < η := lt_min ha hb
  have hη1 : η < 1 := (min_le_left _ _).trans_lt ha1
  have hmatch (p : S1) (ρ : Real) (hρ : |ρ - 1| < η) :
      ρ • (p : E2) ∈ d.source ∧
      d (ρ • (p : E2)) = T (q p, s * ((1 - ρ ^ 2) / (2 * ρ))) ∧
      g (ρ • (p : E2)) = f (d (ρ • (p : E2))) := by
    obtain ⟨hx, ht, hdval⟩ := hdclock p ρ (hρ.trans_le (min_le_left a b))
    refine ⟨hx, hdval, ?_⟩
    rw [hdval, hcylinder _ _ (abs_lt.mp ht), hgclock p ρ (hρ.trans_le (min_le_right a b))]
    rfl
  let R := 1 + η / 2
  have hR : (1 : Real) < R := by dsimp [R]; linarith
  have hsmall {ρ : Real} (hlo : 1 ≤ ρ) (hhi : ρ ≤ R) : |ρ - 1| < η := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    dsimp [R] at hhi
    linarith
  have hradial {x : E2} (hx : 0 < ‖x‖) :
      ‖x‖ • (CircleCollar.direction x : E2) = x := by
    rw [CircleCollar.direction_coe (norm_pos_iff.mp hx), smul_smul,
      mul_inv_cancel₀ hx.ne', one_smul]
  have hRsource : closedBall (0 : E2) R ⊆ d.source := by
    intro x hx
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hdsource (mem_closedBall_zero_iff.mpr hx1)
    · have hpos : 0 < ‖x‖ := by linarith [lt_of_not_ge hx1]
      have hh := (hmatch (CircleCollar.direction x) ‖x‖
        (hsmall (le_of_lt (lt_of_not_ge hx1)) (mem_closedBall_zero_iff.mp hx))).1
      rwa [hradial hpos] at hh
  have hagree (x : E2) (hx : 1 ≤ ‖x‖) (hxR : ‖x‖ ≤ R) : g x = f (d x) := by
    have hh := (hmatch (CircleCollar.direction x) ‖x‖ (hsmall hx hxR)).2.2
    rwa [hradial (by linarith)] at hh
  obtain ⟨f', hf', hf'cap, hf'off, hf'range⟩ := exists_smooth_sphere_disk_splicing
    hf d hd hdi zero_lt_one hR hRsource g hg hginj.injOn
      (fun x _ => hgder x) hagree hdisjoint
  refine ⟨d, hd, hdi, hdsource, hdclosed, hdball, hdcenter, hdnegative, q, g, hg, hginj,
    hgder, ?_, hgnegative, hgwidth, ⟨η, hη, hη1, hmatch⟩, hdisjoint, hgrange,
    f', hf', hf'cap, hf'off, hf'range⟩
  intro p
  refine ⟨?_, hgboundary p⟩
  simpa only [one_smul] using (hmatch p 1 (by simpa using hη)).2.2

theorem exists_capped_sphere_of_cylindrical_tube_with_disk_and_range
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {ε : Real} (hε : 0 < ε)
    {τ : Real} (hτ : 0 < τ)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 -> Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (hcylinder : ∀ p t, t ∈ Ioo (-ε) ε ->
      f (T (p, t)) = (c + t) • v + (γ p : E3))
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hintersection :
      ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => T (p, 0)))
    (e : OpenPartialHomeomorph E2 S2)
    (hesource : closedBall 0 1 ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hecenter : range (fun p : S1 => T (p, 0)) = e '' sphere (0 : E2) 1)
    (henegative : ∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ e '' ball 0 1) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      closedBall 0 1 ⊆ d.source ∧
      d '' closedBall 0 1 = e '' closedBall 0 1 ∧
      d '' ball 0 1 = e '' ball 0 1 ∧
      range (fun p : S1 => T (p, 0)) = d '' sphere (0 : E2) 1 ∧
      (∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ d '' ball 0 1) ∧
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
        ∃ (s : Real) (hs : s < 0), ∃ g : E2 -> E3,
          ContDiff Real ∞ g ∧ Injective g ∧
          (∀ x, Injective (fderiv Real g x)) ∧
          (∀ p : S1, g p = f (d p) ∧ g p = c • v + (γ (q p) : E3)) ∧
          (∀ x, ‖x‖ < 1 -> inner Real v (g x) < c) ∧
          (∀ x, |inner Real v (g x) - c| < τ) ∧
          (∃ η : Real, 0 < η ∧ η < 1 ∧
            ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η ->
              ρ • (p : E2) ∈ d.source ∧
              d (ρ • (p : E2)) = T (q p, s * ((1 - ρ ^ 2) / (2 * ρ))) ∧
              g (ρ • (p : E2)) = f (d (ρ • (p : E2)))) ∧
          Disjoint (g '' ball 0 1) (f '' (d '' ball 0 1)ᶜ) ∧
          g '' closedBall (0 : E2) 1 =
            Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs.ne A ''
              ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
                {p : S2 | 0 ≤ inner Real v (p : E3)}) ∧
          ∃ f' : S2 -> E3,
            _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f' ∧
            (∀ x ∈ closedBall 0 1, f' (d x) = g x) ∧
            (∀ y ∉ d '' ball 0 1, f' y = f y) ∧
            range f' = g '' closedBall 0 1 ∪ f '' (d '' ball 0 1)ᶜ := by
  obtain ⟨δ, hδ, hcap⟩ :=
    exists_capped_sphere_of_cylindrical_tube_with_disk_and_range_for_small_scale hf hv c hε hτ
      T hT hTi hsource γ hγ hcylinder A hboundary hintersection
      e hesource he hei hecenter henegative
  have hsδ : -δ < -δ / 2 := by linarith
  have hs : -δ / 2 < 0 := by linarith
  obtain ⟨d, hd, hdi, hds, hdc, hdb, hdcenter, hdneg, q, g, hg⟩ := hcap (-δ / 2) hsδ hs
  exact ⟨d, hd, hdi, hds, hdc, hdb, hdcenter, hdneg, q, -δ / 2, hs, g, hg⟩

theorem exists_capped_sphere_of_cylindrical_tube_with_disk
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {ε : Real} (hε : 0 < ε)
    {τ : Real} (hτ : 0 < τ)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 -> Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (hcylinder : ∀ p t, t ∈ Ioo (-ε) ε ->
      f (T (p, t)) = (c + t) • v + (γ p : E3))
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hintersection :
      ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => T (p, 0)))
    (e : OpenPartialHomeomorph E2 S2)
    (hesource : closedBall 0 1 ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hecenter : range (fun p : S1 => T (p, 0)) = e '' sphere (0 : E2) 1)
    (henegative : ∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ e '' ball 0 1) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      closedBall 0 1 ⊆ d.source ∧
      d '' closedBall 0 1 = e '' closedBall 0 1 ∧
      d '' ball 0 1 = e '' ball 0 1 ∧
      range (fun p : S1 => T (p, 0)) = d '' sphere (0 : E2) 1 ∧
      (∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ d '' ball 0 1) ∧
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
        ∃ s : Real, s < 0 ∧ ∃ g : E2 -> E3,
          ContDiff Real ∞ g ∧ Injective g ∧
          (∀ x, Injective (fderiv Real g x)) ∧
          (∀ p : S1, g p = f (d p) ∧ g p = c • v + (γ (q p) : E3)) ∧
          (∀ x, ‖x‖ < 1 -> inner Real v (g x) < c) ∧
          (∀ x, |inner Real v (g x) - c| < τ) ∧
          (∃ η : Real, 0 < η ∧ η < 1 ∧
            ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η ->
              ρ • (p : E2) ∈ d.source ∧
              d (ρ • (p : E2)) = T (q p, s * ((1 - ρ ^ 2) / (2 * ρ))) ∧
              g (ρ • (p : E2)) = f (d (ρ • (p : E2)))) ∧
          Disjoint (g '' ball 0 1) (f '' (d '' ball 0 1)ᶜ) ∧
          ∃ f' : S2 -> E3,
            _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f' ∧
            (∀ x ∈ closedBall 0 1, f' (d x) = g x) ∧
            (∀ y ∉ d '' ball 0 1, f' y = f y) ∧
            range f' = g '' closedBall 0 1 ∪ f '' (d '' ball 0 1)ᶜ := by
  obtain ⟨d, hd, hdi, hds, hdc, hdb, hdcenter, hdneg,
    q, s, hs, g, hg, hgi, hgd, hgb, hgn, hgw, hgcollar, hgdis, _, hsplice⟩ :=
    exists_capped_sphere_of_cylindrical_tube_with_disk_and_range hf hv c hε hτ
      T hT hTi hsource γ hγ hcylinder A hboundary hintersection
      e hesource he hei hecenter henegative
  exact ⟨d, hd, hdi, hds, hdc, hdb, hdcenter, hdneg,
    q, s, hs, g, hg, hgi, hgd, hgb, hgn, hgw, hgcollar, hgdis, hsplice⟩

theorem exists_capped_sphere_of_cylindrical_tube
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {ε : Real} (hε : 0 < ε)
    {τ : Real} (hτ : 0 < τ)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 -> Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (hcylinder : ∀ p t, t ∈ Ioo (-ε) ε ->
      f (T (p, t)) = (c + t) • v + (γ p : E3))
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hintersection :
      ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => T (p, 0))) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      closedBall 0 1 ⊆ d.source ∧
      range (fun p : S1 => T (p, 0)) = d '' sphere (0 : E2) 1 ∧
      (∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ d '' ball 0 1) ∧
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
        ∃ s : Real, s < 0 ∧ ∃ g : E2 -> E3,
          ContDiff Real ∞ g ∧ Injective g ∧
          (∀ x, Injective (fderiv Real g x)) ∧
          (∀ p : S1, g p = f (d p) ∧ g p = c • v + (γ (q p) : E3)) ∧
          (∀ x, ‖x‖ < 1 -> inner Real v (g x) < c) ∧
          (∀ x, |inner Real v (g x) - c| < τ) ∧
          (∃ η : Real, 0 < η ∧ η < 1 ∧
            ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η ->
              ρ • (p : E2) ∈ d.source ∧
              d (ρ • (p : E2)) = T (q p, s * ((1 - ρ ^ 2) / (2 * ρ))) ∧
              g (ρ • (p : E2)) = f (d (ρ • (p : E2)))) ∧
          Disjoint (g '' ball 0 1) (f '' (d '' ball 0 1)ᶜ) ∧
          ∃ f' : S2 -> E3,
            _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f' ∧
            (∀ x ∈ closedBall 0 1, f' (d x) = g x) ∧
            (∀ y ∉ d '' ball 0 1, f' y = f y) ∧
            range f' = g '' closedBall 0 1 ∪ f '' (d '' ball 0 1)ᶜ := by
  obtain ⟨e, hesource, he, hei, hecenter, henegative⟩ :=
    exists_inward_disk_of_sphere_tube hε T hT hTi hsource
  obtain ⟨d, hd, hdi, hds, _, _, hdcenter, hdnegative, hcap⟩ :=
    exists_capped_sphere_of_cylindrical_tube_with_disk hf hv c hε hτ
      T hT hTi hsource γ hγ hcylinder A hboundary hintersection
      e hesource he hei hecenter henegative
  exact ⟨d, hd, hdi, hds, hdcenter, hdnegative, hcap⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
