import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubeFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSmoothRestriction









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_end_aligned_stack
    (e : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (heh : ∀ p ∈ e.source, (e p).2 = p.2)
    (hes : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ e.source)
    (ell top eta d : ℝ) (hlt : ell < top)
    (heta : 0 < eta) (hd : 0 < d) (hdeta : d < eta)
    (c : ℝ → UnitCircle → E2)
    (F : PlanarSchoenfliesFamilyData c (ell - 2 * eta) (top + 2 * eta))
    (G : PlanarFamilyGraphChart F)
    (hboundary : ∀ z ∈ Icc (ell - d) (ell + d),
      range (fun q : UnitCircle => (e (q.1, z)).1) = range (c z)) :
    ∃ (r gamma : ℝ)
      (U : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
      (phase : ℝ → Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞),
      1 < r ∧ 0 < gamma ∧ gamma < (top - ell) / 8 ∧ gamma < eta ∧
      U.source = ball (0 : E2) r ×ˢ (univ : Set ℝ) ∧
      ContDiffOn ℝ ∞ U U.source ∧
      ContDiffOn ℝ ∞ U.symm U.target ∧
      (∀ p, (U p).2 = p.2) ∧
      (∀ p ∈ ball (0 : E2) r ×ˢ Ioo (ell - gamma) (ell + gamma),
        p ∈ e.source ∧ U p = e p) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => phase p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => (phase p.1).symm p.2) ∧
      (∀ z ∈ Icc ell (top + gamma), ∀ q : UnitCircle,
        U (q.1, z) = (c z (phase z q), z)) ∧
      U '' (ball (0 : E2) 1 ×ˢ ({top} : Set ℝ)) =
        (fun x : E2 => (F.chart top x, top)) '' ball (0 : E2) 1 ∧
      U '' (closedBall (0 : E2) 1 ×ˢ ({top} : Set ℝ)) =
        (fun x : E2 => (F.chart top x, top)) '' closedBall (0 : E2) 1 := by
  classical
  let P0 := ContinuousLinearEquiv.prodComm ℝ E2 ℝ
  let e1 := (P0.toHomeomorph.transOpenPartialHomeomorph G.chart).transHomeomorph
    P0.symm.toHomeomorph
  have he1apply (p : E2 × ℝ) : e1 p = (F.chart p.2 p.1, p.2) := by
    change ((G.chart (p.2, p.1)).2, (G.chart (p.2, p.1)).1) = _
    rw [G.chart_apply]
  have he1source : e1.source = ball (0 : E2) G.radius ×ˢ
      Ioo (ell - 2 * eta - G.margin) (top + 2 * eta + G.margin) := by
    ext p
    change (p.2, p.1) ∈ G.chart.source ↔ _
    rw [G.source_eq]
    exact and_comm
  have he1 : ContDiffOn ℝ ∞ e1 e1.source :=
    P0.symm.contDiff.comp_contDiffOn
      (G.smooth.comp P0.contDiff.contDiffOn (fun _ hp => hp))
  have he1i : ContDiffOn ℝ ∞ e1.symm e1.target :=
    P0.symm.contDiff.comp_contDiffOn
      (G.smooth_symm.comp P0.contDiff.contDiffOn (fun _ hp => hp))
  have he1h (p : E2 × ℝ) : (e1 p).2 = p.2 := by rw [he1apply]
  have he1ih (p : E2 × ℝ) (hp : p ∈ e1.target) : (e1.symm p).2 = p.2 := by
    have hh := he1h (e1.symm p)
    rw [e1.right_inv hp] at hh
    exact hh.symm
  have he1s {z : ℝ} (hz : z ∈ Icc (ell - 2 * eta) (top + 2 * eta))
      {x : E2} (hx : x ∈ closedBall (0 : E2) 1) : (x, z) ∈ e1.source := by
    rw [he1source]
    exact ⟨closedBall_subset_ball G.one_lt_radius hx, G.height_mem_interval hz⟩
  have hzwide {z : ℝ} (hz : z ∈ Icc (ell - d) (ell + d)) :
      z ∈ Icc (ell - 2 * eta) (top + 2 * eta) := by
    constructor <;> linarith [hz.1, hz.2]
  let f := e.trans e1.symm
  have hf : ContDiffOn ℝ ∞ f f.source :=
    he1i.comp (he.mono inter_subset_left) (fun _ hp => hp.2)
  have hfi : ContDiffOn ℝ ∞ f.symm f.target :=
    hei.comp (he1.mono inter_subset_left) (fun _ hp => hp.2)
  have hfh (p : E2 × ℝ) (hp : p ∈ f.source) : (f p).2 = p.2 := by
    exact (he1ih (e p) hp.2).trans (heh p hp.1)
  have hregion (z : ℝ) (hz : z ∈ Icc (ell - d) (ell + d))
      (A : Set E2) (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (fun x : E2 => (e (x, z)).1) '' A = F.chart z '' A := by
    obtain ⟨B, hB, _, _, _⟩ := exists_saddle_end_fiber_chart e he hei heh z
      (fun x hx => hes ⟨hx, mem_univ _⟩)
    have hBimage (S : Set E2) : B.chart '' S = (fun x : E2 => (e (x, z)).1) '' S :=
      image_congr (fun x _ => hB x)
    have hBboundary : B.boundary = range (c z) := by
      change B.chart '' sphere 0 1 = _
      rw [hBimage]
      calc
        (fun x : E2 => (e (x, z)).1) '' sphere 0 1 =
            range (fun q : UnitCircle => (e (q.1, z)).1) := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨⟨x, hx⟩, rfl⟩
          · rintro ⟨q, rfl⟩
            exact ⟨q.1, q.2, rfl⟩
        _ = range (c z) := hboundary z hz
    rcases hA with rfl | rfl | rfl
    · have hb := G.fiber_inside_eq z (hzwide hz) B hBboundary
      change F.chart z '' ball 0 1 = B.chart '' ball 0 1 at hb
      exact (hBimage _).symm.trans hb.symm
    · have hb := G.fiber_closedRegion_eq z (hzwide hz) B hBboundary
      change F.chart z '' closedBall 0 1 = B.chart '' closedBall 0 1 at hb
      exact (hBimage _).symm.trans hb.symm
    · have hb := G.fiberBallNeighborhood_boundary z (hzwide hz)
      change F.chart z '' sphere 0 1 = range (c z) at hb
      exact (hBimage _).symm.trans (hBboundary.trans hb.symm)
  have hAsub (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      A ⊆ closedBall (0 : E2) 1 := by
    rcases hA with rfl | rfl | rfl
    · exact ball_subset_closedBall
    · exact subset_rfl
    · exact sphere_subset_closedBall
  have hmove (z : ℝ) (hz : z ∈ Icc (ell - d) (ell + d))
      (A : Set E2) (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (∀ x ∈ A, (x, z) ∈ f.source ∧ (f (x, z)).1 ∈ A) ∧
      (∀ y ∈ A, (y, z) ∈ f.target ∧ (f.symm (y, z)).1 ∈ A) := by
    have hreg := hregion z hz A hA
    have hsub := hAsub A hA
    constructor
    · intro x hx
      have hxs : (x, z) ∈ e.source := hes ⟨hsub hx, mem_univ _⟩
      have hm : (e (x, z)).1 ∈ F.chart z '' A := by
        rw [← hreg]
        exact ⟨x, hx, rfl⟩
      rcases hm with ⟨y, hy, hyeq⟩
      have hys := he1s (hzwide hz) (hsub hy)
      have heq : e1 (y, z) = e (x, z) := by
        rw [he1apply]
        exact Prod.ext hyeq (heh (x, z) hxs).symm
      have hsrc : (x, z) ∈ f.source := by
        refine ⟨hxs, ?_⟩
        change e (x, z) ∈ e1.target
        rw [← heq]
        exact e1.map_source hys
      refine ⟨hsrc, ?_⟩
      change (e1.symm (e (x, z))).1 ∈ A
      rw [← heq, e1.left_inv hys]
      exact hy
    · intro y hy
      have hys := he1s (hzwide hz) (hsub hy)
      have hm : F.chart z y ∈ (fun x : E2 => (e (x, z)).1) '' A := by
        rw [hreg]
        exact ⟨y, hy, rfl⟩
      rcases hm with ⟨x, hx, hxeq⟩
      have hxs : (x, z) ∈ e.source := hes ⟨hsub hx, mem_univ _⟩
      have heq : e (x, z) = e1 (y, z) := by
        rw [he1apply]
        exact Prod.ext hxeq (heh (x, z) hxs)
      have htar : (y, z) ∈ f.target := by
        refine ⟨hys, ?_⟩
        change e1 (y, z) ∈ e.target
        rw [← heq]
        exact e.map_source hxs
      refine ⟨htar, ?_⟩
      change (e.symm (e1 (y, z))).1 ∈ A
      rw [← heq, e.left_inv hxs]
      exact hx
  obtain ⟨k0, hk0, hk0range, hk0fix⟩ := exists_saddle_end_height_clamp
    (ell - d / 8) (ell + d / 8) (d / 8) (by linarith) (by positivity)
  have hk0I (z : ℝ) : k0 z ∈ Icc (ell - d / 4) (ell + d / 4) := by
    have h := hk0range z
    constructor <;> linarith [h.1, h.2]
  have hKsmall : Icc (ell - d / 4) (ell + d / 4) ⊆ Icc (ell - d) (ell + d) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  have hKsource : closedBall (0 : E2) 1 ×ˢ
      Icc (ell - d / 4) (ell + d / 4) ⊆ f.source := by
    intro p hp
    exact (hmove p.2 (hKsmall hp.2) (closedBall 0 1) (Or.inr (Or.inl rfl))).1 p.1 hp.1 |>.1
  obtain ⟨r, hr, hrsource⟩ := exists_saddle_end_disc_buffer
    (Icc (ell - d / 4) (ell + d / 4)) isCompact_Icc f.source f.open_source hKsource
  obtain ⟨k1, hk1, hk1range, hk1fix⟩ := exists_saddle_end_height_clamp
    (ell - eta) (top + eta) (eta / 2) (by linarith) (by positivity)
  have hk1I (z : ℝ) : k1 z ∈ Icc (ell - 2 * eta) (top + 2 * eta) := by
    have h := hk1range z
    constructor <;> linarith [h.1, h.2]
  obtain ⟨f0, hf0apply, hf0inv, hf0source, hf0target, hf0, hf0i, hf0h⟩ :=
    exists_saddle_end_chart_reparam f hf hfi hfh k0 hk0
  obtain ⟨g1, hg1apply, _, hg1source, _, hg1, hg1i, _⟩ :=
    exists_saddle_end_chart_reparam e1 he1 he1i (fun p _ => he1h p) k1 hk1
  have hf0ih (p : E2 × ℝ) : (f0.symm p).2 = p.2 := by rw [hf0inv]
  have hmove0 (z : ℝ) (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (∀ x ∈ A, (x, z) ∈ f0.source ∧ (f0 (x, z)).1 ∈ A) ∧
      (∀ y ∈ A, (y, z) ∈ f0.target ∧ (f0.symm (y, z)).1 ∈ A) := by
    have h := hmove (k0 z) (hKsmall (hk0I z)) A hA
    constructor
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [hf0source]
        exact (h.1 x hx).1
      · rw [hf0apply]
        exact (h.1 x hx).2
    · intro y hy
      refine ⟨?_, ?_⟩
      · rw [hf0target]
        exact (h.2 y hy).1
      · rw [hf0inv]
        exact (h.2 y hy).2
  let U0 := f0.trans g1
  let V := ball (0 : E2) r ×ˢ (univ : Set ℝ)
  have hVsource : V ⊆ U0.source := by
    intro p hp
    have hfp : (p.1, k0 p.2) ∈ f.source := hrsource ⟨hp.1, hk0I p.2⟩
    have hf0p : p ∈ f0.source := by rw [hf0source]; exact hfp
    have hrad : (f (p.1, k0 p.2)).1 ∈ ball (0 : E2) G.radius := by
      have himg : f (p.1, k0 p.2) ∈ e1.source := (f.map_source hfp).1
      rw [he1source] at himg
      exact himg.1
    refine ⟨hf0p, ?_⟩
    change f0 p ∈ g1.source
    rw [hg1source]
    change ((f0 p).1, k1 (f0 p).2) ∈ e1.source
    rw [hf0apply, he1source]
    exact ⟨hrad, G.height_mem_interval (hk1I p.2)⟩
  let U := U0.restrOpen V (isOpen_ball.prod isOpen_univ)
  have hUsource : U.source = V := inter_eq_right.mpr hVsource
  have hU : ContDiffOn ℝ ∞ U U.source :=
    (hg1.comp (hf0.mono inter_subset_left) (fun _ hp => hp.2)).mono inter_subset_left
  have hUi : ContDiffOn ℝ ∞ U.symm U.target :=
    (hf0i.comp (hg1i.mono inter_subset_left) (fun _ hp => hp.2)).mono inter_subset_left
  have hUapply (p : E2 × ℝ) : U p =
      (F.chart (k1 p.2) (f0 p).1, p.2) := by
    change g1 (f0 p) = _
    rw [hg1apply, hf0h, he1apply]
  have hUh (p : E2 × ℝ) : (U p).2 = p.2 := by rw [hUapply]
  let gamma := min (d / 16) ((top - ell) / 16)
  have hgamma : 0 < gamma := lt_min (by positivity) (by positivity)
  have hgd : gamma < d / 8 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hglt : gamma < (top - ell) / 8 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hgeta : gamma < eta := by linarith
  have hk1saved {z : ℝ} (hz : z ∈ Icc (ell - gamma) (top + gamma)) : k1 z = z :=
    hk1fix (by constructor <;> linarith [hz.1, hz.2])
  have hUold (p : E2 × ℝ)
      (hp : p ∈ ball (0 : E2) r ×ˢ Ioo (ell - gamma) (ell + gamma)) :
      p ∈ e.source ∧ U p = e p := by
    have hk0p : k0 p.2 = p.2 := hk0fix (by
      constructor <;> linarith [hp.2.1, hp.2.2])
    have hk1p : k1 p.2 = p.2 := hk1saved (by
      constructor <;> linarith [hp.2.1, hp.2.2])
    have hfp : p ∈ f.source := by
      have h : (p.1, k0 p.2) ∈ f.source := hrsource ⟨hp.1, hk0I p.2⟩
      simpa only [hk0p, Prod.eta] using h
    refine ⟨hfp.1, ?_⟩
    have hff : f0 p = f p := by
      rw [hf0apply, hk0p]
      exact Prod.ext rfl (hfh p hfp).symm
    rw [hUapply, hk1p, hff]
    have hh : (F.chart p.2 (f p).1, p.2) = e1 (f p) := by
      rw [he1apply, hfh p hfp]
    rw [hh]
    exact e1.right_inv hfp.2
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let P : ℝ × UnitCircle → E2 × ℝ := fun p => (p.2.1, p.1)
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2 × ℝ) ∞ P :=
    (contMDiff_coe_sphere.comp contMDiff_snd).prodMk_space contMDiff_fst
  have hsphere (z : ℝ) (q : UnitCircle) :
      (f0 (q.1, z)).1 ∈ sphere (0 : E2) 1 :=
    (hmove0 z (sphere 0 1) (Or.inr (Or.inr rfl))).1 q.1 q.2 |>.2
  have hisphere (z : ℝ) (q : UnitCircle) :
      (f0.symm (q.1, z)).1 ∈ sphere (0 : E2) 1 :=
    (hmove0 z (sphere 0 1) (Or.inr (Or.inr rfl))).2 q.1 q.2 |>.2
  let phaseF : ℝ × UnitCircle → UnitCircle := fun p =>
    ⟨(f0 (P p)).1, hsphere p.1 p.2⟩
  let phaseI : ℝ × UnitCircle → UnitCircle := fun p =>
    ⟨(f0.symm (P p)).1, hisphere p.1 p.2⟩
  have hphaseF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞ phaseF := by
    have hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => (f0 (P p)).1) := by
      apply contMDiffOn_univ.mp
      apply contDiff_fst.contMDiff.comp_contMDiffOn
      exact hf0.contMDiffOn.comp hP.contMDiffOn (fun p _ =>
        (hmove0 p.1 (sphere 0 1) (Or.inr (Or.inr rfl))).1 p.2.1 p.2.2 |>.1)
    exact hh.codRestrict_sphere (fun p => hsphere p.1 p.2)
  have hphaseI : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞ phaseI := by
    have hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => (f0.symm (P p)).1) := by
      apply contMDiffOn_univ.mp
      apply contDiff_fst.contMDiff.comp_contMDiffOn
      exact hf0i.contMDiffOn.comp hP.contMDiffOn (fun p _ =>
        (hmove0 p.1 (sphere 0 1) (Or.inr (Or.inr rfl))).2 p.2.1 p.2.2 |>.1)
    exact hh.codRestrict_sphere (fun p => hisphere p.1 p.2)
  have hphaseleft (z : ℝ) (q : UnitCircle) : phaseI (z, phaseF (z, q)) = q := by
    apply Subtype.ext
    have hsrc := (hmove0 z (sphere 0 1) (Or.inr (Or.inr rfl))).1 q.1 q.2 |>.1
    change (f0.symm ((f0 (q.1, z)).1, z)).1 = q.1
    have hp : ((f0 (q.1, z)).1, z) = f0 (q.1, z) :=
      Prod.ext rfl (hf0h (q.1, z)).symm
    rw [hp, f0.left_inv hsrc]
  have hphaseright (z : ℝ) (q : UnitCircle) : phaseF (z, phaseI (z, q)) = q := by
    apply Subtype.ext
    have htar := (hmove0 z (sphere 0 1) (Or.inr (Or.inr rfl))).2 q.1 q.2 |>.1
    change (f0 ((f0.symm (q.1, z)).1, z)).1 = q.1
    have hp : ((f0.symm (q.1, z)).1, z) = f0.symm (q.1, z) :=
      Prod.ext rfl (hf0ih (q.1, z)).symm
    rw [hp, f0.right_inv htar]
  let phase : ℝ → Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞ := fun z => {
    toEquiv := {
      toFun := fun q => phaseF (z, q)
      invFun := fun q => phaseI (z, q)
      left_inv := hphaseleft z
      right_inv := hphaseright z }
    contMDiff_toFun := hphaseF.comp (contMDiff_const.prodMk contMDiff_id)
    contMDiff_invFun := hphaseI.comp (contMDiff_const.prodMk contMDiff_id) }
  have hUboundary (z : ℝ) (hz : z ∈ Icc ell (top + gamma)) (q : UnitCircle) :
      U (q.1, z) = (c z (phase z q), z) := by
    rw [hUapply, hk1saved ⟨by linarith [hz.1], hz.2⟩]
    change (F.chart z (phase z q).1, z) = _
    rw [F.chart_boundary z (by constructor <;> linarith [hz.1, hz.2]) (phase z q)]
  have hUimage (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      U '' (A ×ˢ ({top} : Set ℝ)) = (fun x : E2 => (F.chart top x, top)) '' A := by
    have hktop : k1 top = top := hk1saved ⟨by linarith, by linarith⟩
    have hm := hmove0 top A hA
    ext p
    constructor
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
      have hzt : z = top := hz
      subst z
      refine ⟨(f0 (x, top)).1, (hm.1 x hx).2, ?_⟩
      rw [hUapply, hktop]
    · rintro ⟨y, hy, rfl⟩
      let x := (f0.symm (y, top)).1
      have hxs : x ∈ A := (hm.2 y hy).2
      have hinv : f0 (x, top) = (y, top) := by
        have hp : (x, top) = f0.symm (y, top) := Prod.ext rfl (hf0ih (y, top)).symm
        rw [hp]
        exact f0.right_inv (hm.2 y hy).1
      refine ⟨(x, top), ⟨hxs, mem_singleton _⟩, ?_⟩
      rw [hUapply, hktop, hinv]
  exact ⟨r, gamma, U, phase, hr, hgamma, hglt, hgeta, hUsource,
    hU, hUi, hUh, hUold, hphaseF, hphaseI, hUboundary,
    hUimage (ball 0 1) (Or.inl rfl),
    hUimage (closedBall 0 1) (Or.inr (Or.inl rfl))⟩

end PoincareConjecture.M25.Topology3D
