import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarBallChartExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarFamilyHeightLift












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞





theorem exists_nonnested_height_first_ambient_extension
    (u : UnitTwoSphere)
    (E : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hE : ContDiffOn ℝ ∞ E E.source)
    (hEi : ContDiffOn ℝ ∞ E.symm E.target)
    (htime : ∀ p ∈ E.source, (E p).1 = p.1)
    (htimei : ∀ p ∈ E.target, (E.symm p).1 = p.1)
    (a l r b : ℝ) (hal : a < l) (hrb : r < b)
    (hsource : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ E.source)
    (htarget : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ E.target)
    (himage : ∀ z ∈ Icc l r,
      E '' (({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1) =
        ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 ∧
      E.symm '' (({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1) =
        ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1)
    (B : BallNeighborhoodChart E2 E2) (s : ℝ) (hs : s ∈ Ioo l r)
    (hB : ∀ x : E2, B.chart x = (E (s, x)).2) :
    ∃ G : D3,
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((E (z, x)).2, z)) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((E.symm (z, x)).2, z)) ∧
      G '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) ∧
      G.symm '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
  have hsa : s ∈ Ioo a b := by
    exact ⟨lt_trans hal hs.1, lt_trans hs.2 hrb⟩
  obtain ⟨Phi, hPhi, hPhi0, htracks, hsupport, hlinear⟩ :=
    exists_ambient_isotopy_of_chart E hE hEi htime
      (0 : E2 →L[ℝ] ℝ) (fun _ _ => rfl)
      (isCompact_closedBall (0 : E2) 1) hsa hsource
  obtain ⟨H, hH, hHi, hHinside, hHclosed, hHdisc⟩ :=
    exists_saddle_planar_ball_chart_extension B
  let F : ℝ → D2 := fun t => H.trans (Phi t)
  have hFtrack (x : E2) (hx : x ∈ closedBall (0 : E2) 1)
      (z : ℝ) (hz : z ∈ Icc l r) :
      F z x = (E (z, x)).2 := by
    change Phi z (H x) = _
    rw [hH hx, hB x]
    exact htracks x hx z ⟨lt_of_lt_of_le hal hz.1, lt_of_le_of_lt hz.2 hrb⟩
  have hFinv : ContDiff ℝ ∞
      (fun p : ℝ × E2 => (F p.1).symm p.2) := by
    have hPhiInv := planarDiffeomorphFamily_contDiff_symm Phi hPhi
    change ContDiff ℝ ∞
      (fun p : ℝ × E2 => H.symm ((Phi p.1).symm p.2))
    exact H.symm.contDiff.comp hPhiInv
  have hF : ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2) := by
    change ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 (H p.2))
    exact hPhi.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd))
  let Q := planarFamilyGraphDiffeomorph F hF hFinv
  let L := heightPlaneCoordinates u
  let G : D3 := (L.toDiffeomorph.trans Q).trans L.symm.toDiffeomorph
  have hG (x : E2) (z : ℝ) :
      G (L.symm (x, z)) = L.symm (F z x, z) := by
    change L.symm (Q (L (L.symm (x, z)))) = _
    rw [L.apply_symm_apply]
    rfl
  have hGi (x : E2) (z : ℝ) :
      G.symm (L.symm (x, z)) = L.symm ((F z).symm x, z) := by
    change L.symm (Q.symm (L (L.symm (x, z)))) = _
    rw [L.apply_symm_apply]
    rfl
  have hstack :
      G '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases p with ⟨x, z⟩
      have hx : x ∈ closedBall (0 : E2) 1 := by simpa using hp.1
      have hz : z ∈ Icc l r := by simpa using hp.2
      have hout : E (z, x) ∈ ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 := by
        rw [← (himage z hz).1]
        exact ⟨(z, x), ⟨rfl, hx⟩, rfl⟩
      refine ⟨((E (z, x)).2, z), ⟨hout.2, hz⟩, ?_⟩
      · rw [hG, hFtrack x hx z hz]
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, z⟩
      have hx : x ∈ closedBall (0 : E2) 1 := by simpa using hp.1
      have hz : z ∈ Icc l r := by simpa using hp.2
      have hzab : z ∈ Icc a b :=
        ⟨le_trans hal.le hz.1, le_trans hz.2 hrb.le⟩
      have hyE : (z, x) ∈ E.target := htarget ⟨hzab, hx⟩
      have hpre : E.symm (z, x) ∈ ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 := by
        rw [← (himage z hz).2]
        exact ⟨(z, x), ⟨rfl, hx⟩, rfl⟩
      have hfirst : (E.symm (z, x)).1 = z := htimei (z, x) hyE
      have hpair : E.symm (z, x) = (z, (E.symm (z, x)).2) :=
        Prod.ext hfirst rfl
      have heq : E (z, (E.symm (z, x)).2) = (z, x) := by
        rw [← hpair]
        exact E.right_inv hyE
      refine ⟨L.symm ((E.symm (z, x)).2, z), ?_, ?_⟩
      · exact ⟨((E.symm (z, x)).2, z), ⟨hpre.2, hz⟩, rfl⟩
      · rw [hG, hFtrack (E.symm (z, x)).2 hpre.2 z hz, heq]
  have hstackInv :
      G.symm '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
    calc
      G.symm '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
          G.symm '' (G '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc l r))) := by
            rw [hstack]
      _ = L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
        rw [image_image]
        simp only [G.symm_apply_apply, image_id']
  refine ⟨G, ?_, ?_, hstack, hstackInv⟩
  · intro x hx z hz
    rw [hG, hFtrack x hx z hz]
  · intro y hy z hz
    have hzab : z ∈ Icc a b :=
      ⟨le_trans hal.le hz.1, le_trans hz.2 hrb.le⟩
    have hyE : (z, y) ∈ E.target := htarget ⟨hzab, hy⟩
    have hpre : E.symm (z, y) ∈ ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 := by
      rw [← (himage z hz).2]
      exact ⟨(z, y), ⟨rfl, hy⟩, rfl⟩
    have hfirst : (E.symm (z, y)).1 = z := htimei (z, y) hyE
    have hpair : E.symm (z, y) = (z, (E.symm (z, y)).2) :=
      Prod.ext hfirst rfl
    have heq : E (z, (E.symm (z, y)).2) = (z, y) := by
      rw [← hpair]
      exact E.right_inv hyE
    rw [hGi]
    have htrack := hFtrack (E.symm (z, y)).2 hpre.2 z hz
    rw [heq] at htrack
    have htrack' : F z (E.symm (z, y)).2 = y := by simpa using htrack
    have hinvtrack : (F z).symm y = (E.symm (z, y)).2 := by
      exact (congrArg (F z).symm htrack'.symm).trans
        ((F z).symm_apply_apply _)
    rw [hinvtrack]



theorem exists_nonnested_product_ambient_extension
    (u : UnitTwoSphere)
    (e : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (heh : ∀ p ∈ e.source, (e p).2 = p.2)
    (hehi : ∀ p ∈ e.target, (e.symm p).2 = p.2)
    (a l r b : ℝ) (hal : a < l) (hrb : r < b)
    (hsource : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ e.source)
    (htarget : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ e.target)
    (himage : ∀ z ∈ Icc l r,
      e '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) ∧
      e.symm '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))
    (B : BallNeighborhoodChart E2 E2) (s : ℝ) (hs : s ∈ Ioo l r)
    (hB : ∀ x : E2, B.chart x = (e (x, s)).1) :
    ∃ G : D3,
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((e (x, z)).1, z)) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((e.symm (x, z)).1, z)) ∧
      G '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) ∧
      G.symm '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
  let E : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2) := {
    toFun := fun p => (p.1, (e (p.2, p.1)).1)
    invFun := fun p => (p.1, (e.symm (p.2, p.1)).1)
    source := {p | (p.2, p.1) ∈ e.source}
    target := {p | (p.2, p.1) ∈ e.target}
    map_source' := by
      intro p hp
      change ((e (p.2, p.1)).1, p.1) ∈ e.target
      have hmap := e.map_source hp
      have hsecond := heh (p.2, p.1) hp
      have hpair : ((e (p.2, p.1)).1, p.1) = e (p.2, p.1) := by
        apply Prod.ext
        · rfl
        · exact hsecond.symm
      rw [hpair]
      exact hmap
    map_target' := by
      intro p hp
      change ((e.symm (p.2, p.1)).1, p.1) ∈ e.source
      have hmap := e.map_target hp
      have hsecond := hehi (p.2, p.1) hp
      have hpair : ((e.symm (p.2, p.1)).1, p.1) = e.symm (p.2, p.1) := by
        apply Prod.ext
        · rfl
        · exact hsecond.symm
      rw [hpair]
      exact hmap
    left_inv' := by
      intro p hp
      change (p.1, (e.symm ((e (p.2, p.1)).1, p.1)).1) = p
      apply Prod.ext
      · rfl
      · have hpair : ((e (p.2, p.1)).1, p.1) = e (p.2, p.1) := by
          apply Prod.ext
          · rfl
          · exact (heh (p.2, p.1) hp).symm
        rw [hpair, e.left_inv hp]
    right_inv' := by
      intro p hp
      change (p.1, (e ((e.symm (p.2, p.1)).1, p.1)).1) = p
      apply Prod.ext
      · rfl
      · have hpair : ((e.symm (p.2, p.1)).1, p.1) = e.symm (p.2, p.1) := by
          apply Prod.ext
          · rfl
          · exact (hehi (p.2, p.1) hp).symm
        rw [hpair, e.right_inv hp]
    open_source := e.open_source.preimage (continuous_snd.prodMk continuous_fst)
    open_target := e.open_target.preimage (continuous_snd.prodMk continuous_fst)
    continuousOn_toFun := by
      have hs : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => e (p.2, p.1))
          {p | (p.2, p.1) ∈ e.source} :=
        he.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => hp)
      exact (contDiff_fst.contDiffOn.prodMk hs.fst).continuousOn
    continuousOn_invFun := by
      have hs : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => e.symm (p.2, p.1))
          {p | (p.2, p.1) ∈ e.target} :=
        hei.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => hp)
      exact (contDiff_fst.contDiffOn.prodMk hs.fst).continuousOn }
  have hEsource (p : ℝ × E2) (hp : p ∈ E.source) :
      (p.2, p.1) ∈ e.source := hp
  have hEtarget (p : ℝ × E2) (hp : p ∈ E.target) :
      (p.2, p.1) ∈ e.target := hp
  have hEsource' (p : ℝ × E2) (hp : (p.2, p.1) ∈ e.source) :
      p ∈ E.source := hp
  have hEtarget' (p : ℝ × E2) (hp : (p.2, p.1) ∈ e.target) :
      p ∈ E.target := hp
  have hEsmooth : ContDiffOn ℝ ∞ E E.source := by
    change ContDiffOn ℝ ∞ (fun p : ℝ × E2 =>
      (p.1, (e (p.2, p.1)).1)) E.source
    have hs : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => e (p.2, p.1)) E.source :=
      he.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
        (fun p hp => hEsource p hp)
    exact contDiff_fst.contDiffOn.prodMk hs.fst
  have hEis : ContDiffOn ℝ ∞ E.symm E.target := by
    change ContDiffOn ℝ ∞ (fun p : ℝ × E2 =>
      (p.1, (e.symm (p.2, p.1)).1)) E.target
    have hs : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => e.symm (p.2, p.1)) E.target :=
      hei.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
        (fun p hp => hEtarget p hp)
    exact contDiff_fst.contDiffOn.prodMk hs.fst
  have hEheight (p : ℝ × E2) (_hp : p ∈ E.source) : (E p).1 = p.1 := by
    rfl
  have hEheighti (p : ℝ × E2) (_hp : p ∈ E.target) :
      (E.symm p).1 = p.1 := by
    rfl
  have hEsrc : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ E.source := by
    intro p hp
    exact hEsource' p (hsource ⟨hp.2, hp.1⟩)
  have hEtgt : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ E.target := by
    intro p hp
    exact hEtarget' p (htarget ⟨hp.2, hp.1⟩)
  have hEimage (z : ℝ) (hz : z ∈ Icc l r) :
      E '' (({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1) =
        ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 ∧
      E.symm '' (({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1) =
        ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 := by
    rcases himage z hz with ⟨hf, hi⟩
    constructor
    · ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases q with ⟨qz, qx⟩
        have hqz : qz = z := by simpa using hq.1
        subst qz
        have hout : e (qx, z) ∈ closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) := by
          rw [← hf]
          exact ⟨(qx, z), ⟨hq.2, rfl⟩, rfl⟩
        change (z, (e (qx, z)).1) ∈ ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1
        exact ⟨rfl, hout.1⟩
      · rintro ⟨hpz, hpx⟩
        rcases p with ⟨pz, px⟩
        have hpz' : pz = z := by simpa using hpz
        subst pz
        have hin : e.symm (px, z) ∈ closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) := by
          rw [← hi]
          exact ⟨(px, z), ⟨hpx, rfl⟩, rfl⟩
        have hyE : (px, z) ∈ e.target := htarget
          ⟨hpx, ⟨le_trans hal.le hz.1, le_trans hz.2 hrb.le⟩⟩
        have hsecond : (e.symm (px, z)).2 = z := hehi _ hyE
        refine ⟨(z, (e.symm (px, z)).1), ⟨rfl, hin.1⟩, ?_⟩
        dsimp [E]
        have hpair : ((e.symm (px, z)).1, z) = e.symm (px, z) := by
          apply Prod.ext
          · rfl
          · exact hsecond.symm
        rw [hpair, e.right_inv hyE]
    · ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases q with ⟨qz, qx⟩
        have hqz : qz = z := by simpa using hq.1
        subst qz
        have hout : e.symm (qx, z) ∈ closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) := by
          rw [← hi]
          exact ⟨(qx, z), ⟨hq.2, rfl⟩, rfl⟩
        change (z, (e.symm (qx, z)).1) ∈ ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1
        exact ⟨rfl, hout.1⟩
      · rintro ⟨hpz, hpx⟩
        rcases p with ⟨pz, px⟩
        have hpz' : pz = z := by simpa using hpz
        subst pz
        have hin : e (px, z) ∈ closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) := by
          rw [← hf]
          exact ⟨(px, z), ⟨hpx, rfl⟩, rfl⟩
        have hxE : (px, z) ∈ e.source := hsource
          ⟨hpx, ⟨le_trans hal.le hz.1, le_trans hz.2 hrb.le⟩⟩
        have hsecond : (e (px, z)).2 = z := heh _ hxE
        refine ⟨(z, (e (px, z)).1), ⟨rfl, hin.1⟩, ?_⟩
        dsimp [E]
        have hpair : ((e (px, z)).1, z) = e (px, z) := by
          apply Prod.ext
          · rfl
          · exact hsecond.symm
        rw [hpair, e.left_inv hxE]
  have hsB : ∀ x : E2, B.chart x = (E (s, x)).2 := by
    intro x
    change B.chart x = (e (x, s)).1
    exact hB x
  obtain ⟨G, hG, hGi, hstack, hstackInv⟩ :=
    exists_nonnested_height_first_ambient_extension u E hEsmooth hEis
      hEheight hEheighti a l r b hal hrb hEsrc hEtgt hEimage B s hs hsB
  refine ⟨G, ?_, ?_, hstack, hstackInv⟩
  · intro x hx z hz
    rw [hG x hx z hz]
    rfl
  · intro x hx z hz
    rw [hGi x hx z hz]
    rfl

end PoincareConjecture.M25.Topology3D
