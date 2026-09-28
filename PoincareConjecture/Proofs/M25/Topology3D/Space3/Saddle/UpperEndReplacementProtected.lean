import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperCoreLabel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperCapBandTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.TwoProfileEndBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NorthCapEndTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapHeightCompression
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_upper_end_replacement_protected
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) (z : ℝ)
    (hcz : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < z)
    (hseams : ∀ i : Fin D.capCount, (D.cap i).sign = -1 →
      z < (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal)
    (hlevel : IsConnected
      {q : UnitTwoSphere | ⟪(u : E3), psi (q, 0)⟫_ℝ = z})
    (P : SurgeryCapProfile) (tau : ℝ) (htau : 0 < tau)
    (Kcaps : Set E3) (hKcaps : IsClosed Kcaps)
    (hKheight : ∀ y ∈ Kcaps, ⟪(u : E3), y⟫_ℝ < z - tau) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let S : Set E3 := range j
    let R : Set E3 := S ∩ {y | H y ≤ z}
    let E : Set E3 := S ∩ {y | z ≤ H y}
    let L := heightPlaneCoordinates u
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun t => (P.horizontal_pos t).ne') (fun x => (P.vertical_pos x).ne')
    ∃ (i : Fin D.capCount) (r gamma o w lambda : ℝ)
      (T : OpenPartialHomeomorph (E2 × ℝ) E3)
      (B : BallNeighborhoodChart E2 E2)
      (A N : BallNeighborhoodChart E3 E3)
      (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (K : Set E3),
    let C := D.cap i
    let ell := C.cutHeight - C.removal
    let shared : Set E3 :=
      (fun q : UnitTwoSphere => T ((P.model q).1, z - lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let replacement : Set E3 :=
      (fun q : UnitTwoSphere => T ((P.model q).1, z - lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    C.sign = -1 ∧ (∀ k : Fin D.capCount, (D.cap k).sign = -1 ↔ k = i) ∧
    1 < r ∧ 0 < gamma ∧ gamma < (ell - z) / 8 ∧
    0 < o ∧ o ≤ C.overlapWidth ∧ C.scale * o < gamma / 2 ∧
    0 < w ∧ w ≤ C.collarWidth ∧ |C.beta| * w < C.scale / 2 ∧
    0 < lambda ∧ lambda * P.heightBound < tau ∧
    lambda * P.heightBound < z - c ∧ lambda * P.heightBound < gamma ∧
    T.source =
      (C.tube.source ∩ (ball (0 : E2) r ×ˢ Ioi (ell - gamma))) ∪
        (ball (0 : E2) r ×ˢ Iio (ell + gamma)) ∧
    closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
    ContDiffOn ℝ ∞ T T.source ∧ ContDiffOn ℝ ∞ T.symm T.target ∧
    (∀ p ∈ T.source, H (T p) = p.2) ∧
    (∀ y ∈ T.target, (T.symm y).2 = H y) ∧
    (∀ p ∈ C.tube.source, ‖p.1‖ < r → ell - gamma < p.2 →
      T p = C.tube p ∧ C.tube p ∈ T.target ∧ T.symm (C.tube p) = p) ∧
    (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < o →
      j (C.sourceChart q) =
        C.profile.capMap T C.cutHeight C.sign C.removal C.scale q) ∧
    (∀ x : E2, ‖x‖ ≤ 1 / 8 → ∀ s : ℝ, |s| < w →
      psi (C.flatChart x, s) =
        T (x, C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s)) ∧
    (∀ t ∈ Icc (z - gamma) ell,
      T '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) = S ∩ {y | H y = t}) ∧
    (fun x : E2 => L.symm (x, z)) '' B.boundary = S ∩ {y | H y = z} ∧
    T '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
      (fun x : E2 => L.symm (x, z)) '' B.inside ∧
    T '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
      (fun x : E2 => L.symm (x, z)) '' B.closedRegion ∧
    A.boundary = E ∪ shared ∧ N.boundary = replacement ∪ shared ∧
    N.chart.source = {y : E3 |
      ((M (heightCoordinates y)).1, z - lambda * (M (heightCoordinates y)).2) ∈ T.source} ∧
    N.chart.target = T.target ∧
    (∀ y : E3, N.chart y =
      T ((M (heightCoordinates y)).1, z - lambda * (M (heightCoordinates y)).2)) ∧
    (∀ y : E3, N.chart.symm y = heightCoordinates.symm
      (M.symm ((T.symm y).1, (z - (T.symm y).2) / lambda))) ∧
    (∀ t ∈ Icc z ell,
      A.closedRegion ∩ {y | H y = t} =
        T '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ))) ∧
    N.closedRegion ⊆ A.closedRegion ∧
    N.closedRegion ⊆ {y : E3 | |H y - z| < tau} ∧
    A.closedRegion ⊆ {y : E3 | z - lambda * P.heightBound ≤ H y} ∧
    Disjoint A.inside S ∧ A.closedRegion ∩ R ⊆ shared ∧
    G '' E = replacement ∧ G.symm '' replacement = E ∧
    (∀ y ∈ shared ∪ R ∪ Kcaps, G y = y ∧ G.symm y = y) ∧
    IsCompact K ∧ K ⊆ (shared ∪ R ∪ Kcaps)ᶜ ∧
    tsupport (fun y => G y - y) ⊆ K ∧
    tsupport (fun y => G.symm y - y) ⊆ K ∧
    G '' S = R ∪ replacement ∧ G.symm '' (R ∪ replacement) = S ∧
    IsCollarEmbedding (fun p => G (psi p)) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let f : UnitTwoSphere → ℝ := fun q => H (j q)
  let c := f D.point
  let S : Set E3 := range j
  let R : Set E3 := S ∩ {y | H y ≤ z}
  let E : Set E3 := S ∩ {y | z ≤ H y}
  let L := heightPlaneCoordinates u
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun t => (P.horizontal_pos t).ne') (fun x => (P.vertical_pos x).ne')
  let Kz : Set UnitTwoSphere := D.sourceCore ∩ {q | z ≤ f q}
  change c < z at hcz
  obtain ⟨i, hsign, hunique, hz, hband, hseam, hcapCore, hreg⟩ :=
    exists_saddle_upper_core_label psi hpsi u D z hcz hseams hlevel
  let C := D.cap i
  let ell := C.cutHeight - C.removal
  change C.sign = -1 at hsign
  change z < ell at hz
  change {q : UnitTwoSphere | f q ∈ Icc z ell} = Kz at hband
  change {q : UnitTwoSphere | f q = ell} = C.sourceSeam at hseam
  change C.sourceCap ∪ Kz = {q : UnitTwoSphere | z ≤ f q} at hcapCore
  have hregular (q : UnitTwoSphere) (hq : f q ∈ Icc z ell) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0 := by
    have hqK : q ∈ Kz :=
      hband ▸ (show q ∈ {q : UnitTwoSphere | f q ∈ Icc z ell} from hq)
    exact hreg q hqK
  obtain ⟨r, gamma, o, w, T, hr, hg, hgap, ho, how, hos, hw, hww, hwb,
      hTsource, hTs, hT, hTi, hTh, hTih, hTold, hcentral, hcollar, hcap, hcircle⟩ :=
    exists_saddle_upper_cap_band_tube psi hpsi u C hsign z hz hseam hregular
  change ∀ p ∈ T.source, H (T p) = p.2 at hTh
  have hcircle' (t : ℝ) (ht : t ∈ Icc (z - gamma) ell) :
      T '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) = S ∩ {y | H y = t} :=
    hcircle t ⟨ht.1, by linarith [ht.2]⟩
  have hcircleZ : T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = S ∩ {y | H y = z} :=
    hcircle' z ⟨by linarith, hz.le⟩
  let e := T.transHomeomorph L.toHomeomorph
  have he : ContDiffOn ℝ ∞ e e.source := L.contDiff.comp_contDiffOn hT
  have hei : ContDiffOn ℝ ∞ e.symm e.target :=
    hTi.comp L.symm.contDiff.contDiffOn (fun _ hp => hp)
  have heh (p : E2 × ℝ) (hp : p ∈ e.source) : (e p).2 = p.2 :=
    (heightPlaneCoordinates_snd u (T p)).trans (hTh p hp)
  obtain ⟨B, hBp, _, _, _⟩ := exists_saddle_end_fiber_chart e he hei heh z
    (fun x hx => hTs ⟨hx, mem_univ _⟩)
  let lift : E2 → E3 := fun x => L.symm (x, z)
  have hBpoint (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      lift (B.chart x) = T (x, z) := by
    rw [hBp]
    exact heightPlaneCoordinates_reconstruct u _ z (hTh _ (hTs ⟨hx, mem_univ _⟩))
  have hBimage (X : Set E2) (hX : X ⊆ closedBall (0 : E2) 1) :
      T '' (X ×ˢ ({z} : Set ℝ)) = lift '' (B.chart '' X) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htz : t = z := ht
      subst t
      exact ⟨B.chart x, ⟨x, hx, rfl⟩, hBpoint x (hX hx)⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨(x, z), ⟨hx, mem_singleton _⟩, (hBpoint x (hX hx)).symm⟩
  have hBboundary : lift '' B.boundary = S ∩ {y | H y = z} :=
    (hBimage (sphere 0 1) sphere_subset_closedBall).symm.trans hcircleZ
  have hBinside : T '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = lift '' B.inside :=
    hBimage (ball 0 1) ball_subset_closedBall
  have hBclosed : T '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = lift '' B.closedRegion :=
    hBimage (closedBall 0 1) subset_rfl
  let m := min tau (min (z - c) gamma)
  have hm : 0 < m := lt_min htau (lt_min (sub_pos.mpr hcz) hg)
  let lambda := m / (2 * (P.heightBound + 1))
  have hl : 0 < lambda := div_pos hm (by linarith [P.one_le_heightBound])
  have hlm : lambda * P.heightBound < m := by
    have heq : lambda * (2 * (P.heightBound + 1)) = m :=
      div_mul_cancel₀ m (by linarith [P.one_le_heightBound])
    nlinarith [P.one_le_heightBound]
  have hlt : lambda * P.heightBound < tau := hlm.trans_le (min_le_left _ _)
  have hlc : lambda * P.heightBound < z - c :=
    hlm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlg : lambda * P.heightBound < gamma :=
    hlm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlgap : lambda * P.heightBound < ell - z := by linarith
  let shared : Set E3 := (fun q : UnitTwoSphere =>
    T ((P.model q).1, z - lambda * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let replacement : Set E3 := (fun q : UnitTwoSphere =>
    T ((P.model q).1, z - lambda * (P.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let rim := T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))
  have hEnd : j '' (C.sourceCap ∪ Kz) = E := by
    rw [hcapCore]
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨mem_range_self q, hq⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      exact ⟨q, hq, rfl⟩
  have hCylinder : T '' (sphere (0 : E2) 1 ×ˢ Icc z ell) = j '' Kz := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hm : T p ∈ S ∩ {y | H y = p.2} :=
        (hcircle' p.2 ⟨by linarith [hp.2.1], hp.2.2⟩) ▸
          ⟨p, ⟨hp.1, mem_singleton _⟩, rfl⟩
      obtain ⟨q, hq⟩ := hm.1
      have hqt : f q = p.2 := (congrArg H hq).trans hm.2
      refine ⟨q, hband ▸ ?_, hq⟩
      change f q ∈ Icc z ell
      rw [hqt]
      exact hp.2
    · rintro ⟨q, hq, rfl⟩
      have hqband : q ∈ {q : UnitTwoSphere | f q ∈ Icc z ell} := hband.symm ▸ hq
      have hm : j q ∈ T '' (sphere (0 : E2) 1 ×ˢ ({f q} : Set ℝ)) :=
        (hcircle' (f q) ⟨by linarith [hqband.1], hqband.2⟩).symm ▸
          ⟨mem_range_self q, rfl⟩
      obtain ⟨p, hp, hpy⟩ := hm
      exact ⟨p, ⟨hp.1, hp.2.symm ▸ hqband⟩, hpy⟩
  let negD := (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph
  let idD := Diffeomorph.refl 𝓘(ℝ, E3) E3 ∞
  let Tm := heightTransportTube T negD idD
  let Hm : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 ((-u : UnitTwoSphere) : E3)
  have hHm (y : E3) : Hm y = -H y := by
    change ⟪((-u : UnitTwoSphere) : E3), y⟫_ℝ = -⟪(u : E3), y⟫_ℝ
    rw [coe_neg_sphere, inner_neg_left]
  have hTmp (p : E2 × ℝ) : Tm p = T (p.1, -p.2) := rfl
  have hTmi (y : E3) : Tm.symm y = ((T.symm y).1, -(T.symm y).2) := rfl
  have hTmt : Tm.target = T.target := by
    ext y
    exact heightTransportTube_mem_target T negD idD y
  have hTms : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ Tm.source :=
    heightTransportTube_closedDisc_source T negD idD hTs
  have hTm : ContDiffOn ℝ ∞ Tm Tm.source := heightTransportTube_contDiffOn T negD idD hT
  have hTminv : ContDiffOn ℝ ∞ Tm.symm Tm.target :=
    heightTransportTube_contDiffOn_symm T negD idD hTi
  have hTmh (p : E2 × ℝ) (hp : p ∈ Tm.source) : Hm (Tm p) = p.2 := by
    have hps : (p.1, -p.2) ∈ T.source :=
      (heightTransportTube_mem_source T negD idD p).mp hp
    rw [hHm, hTmp, hTh (p.1, -p.2) hps]
    exact neg_neg p.2
  have hTmSlice (X : Set E2) (t : ℝ) :
      Tm '' (X ×ˢ ({-t} : Set ℝ)) = T '' (X ×ˢ ({t} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
      have hst : s = -t := hs
      subst s
      exact ⟨(x, t), ⟨hx, mem_singleton _⟩, by rw [hTmp]; simp only [neg_neg]⟩
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
      have hst : s = t := hs
      subst s
      exact ⟨(x, -t), ⟨hx, mem_singleton _⟩, by rw [hTmp]; simp only [neg_neg]⟩
  have hTmBand : Tm '' (sphere (0 : E2) 1 ×ˢ Icc (-ell) (-z)) =
      T '' (sphere (0 : E2) 1 ×ˢ Icc z ell) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact ⟨(x, -t), ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩, rfl⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact ⟨(x, -t), ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩,
        by rw [hTmp]; simp only [neg_neg]⟩
  have hNorthPoint (y : E3) : Tm ((M (heightCoordinates y)).1,
      -z + lambda * (M (heightCoordinates y)).2) =
        T ((M (heightCoordinates y)).1, z - lambda * (M (heightCoordinates y)).2) := by
    rw [hTmp]
    congr 1
    apply Prod.ext
    · rfl
    · ring
  have hProfileImage (X : Set UnitTwoSphere) :
      (fun q : UnitTwoSphere => Tm ((P.model q).1, -z + lambda * (P.model q).2)) '' X =
        (fun q : UnitTwoSphere => T ((P.model q).1, z - lambda * (P.model q).2)) '' X :=
    image_congr (fun q _ => hNorthPoint q)
  obtain ⟨_, A, ov, hov, hov1, _, _, _, _, _, hAb0, hAi, hAc, hCuts, hPatch⟩ :=
    exists_two_profile_end_ball C.profile P (-u) Tm hTms hTm hTminv hTmh
      (-ell) (-z) C.scale lambda (by linarith) C.scale_pos hl
  have hLower : (fun q : UnitTwoSphere =>
      Tm ((C.profile.model q).1, -ell + C.scale * (C.profile.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} = C.cap := by
    rw [hcap]
    apply image_congr
    intro q _
    rw [hTmp]
    congr 1
    apply Prod.ext
    · rfl
    · ring
  have hNorth : (fun y : E3 => Tm ((M (heightCoordinates y)).1,
      -z + lambda * (M (heightCoordinates y)).2)) ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} = shared := by
    simp only [hNorthPoint]
    ext y
    constructor
    · rintro ⟨q, ⟨hqn, hqh⟩, rfl⟩
      exact ⟨⟨q, mem_sphere_zero_iff_norm.mpr hqn⟩, hqh, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, rfl⟩
  have hAb : A.boundary = E ∪ shared := by
    rw [hAb0, hLower, hTmBand, hCylinder, hNorth]
    change (j '' C.sourceCap ∪ j '' Kz) ∪ shared = E ∪ shared
    rw [← image_union, hEnd]
  have hAcut (t : ℝ) (ht : t ∈ Icc z ell) :
      A.closedRegion ∩ {y : E3 | H y = t} = T '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) := by
    have hh := (hCuts (-t) (by constructor <;> linarith [ht.1, ht.2])).2
    change A.closedRegion ∩ {y : E3 | Hm y = -t} =
      Tm '' (closedBall (0 : E2) 1 ×ˢ ({-t} : Set ℝ)) at hh
    have hset : {y : E3 | Hm y = -t} = {y : E3 | H y = t} := by
      ext y
      simp only [mem_ofPred_eq, hHm, neg_inj]
    rw [hset, hTmSlice] at hh
    exact hh
  have hAlower (y : E3) (hy : y ∈ A.closedRegion) : z - lambda * P.heightBound ≤ H y := by
    obtain ⟨p, hp, rfl⟩ := hAc hy
    have hh := hTmh p (hTms ⟨hp.1, mem_univ _⟩)
    rw [hHm] at hh
    linarith [hp.2.2]
  have hAvoid : Disjoint A.inside S := by
    apply disjoint_left.mpr
    intro y hyA hyS
    by_cases hyz : z ≤ H y
    · have hyB : y ∈ A.boundary := hAb.symm ▸ Or.inl ⟨hyS, hyz⟩
      exact disjoint_left.mp A.inside_disjoint_boundary hyA hyB
    · have hyAc : y ∈ A.closedRegion := A.inside_union_boundary ▸ Or.inl hyA
      have hyband : H y ∈ Icc (z - gamma) ell := by
        have hlo := hAlower y hyAc
        constructor <;> linarith [lt_of_not_ge hyz]
      have hyCircle : y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)) :=
        (hcircle' (H y) hyband).symm ▸ ⟨hyS, rfl⟩
      obtain ⟨q, hq, hqy⟩ := hyCircle
      obtain ⟨p, hp, hpy⟩ := hAi hyA
      have hps : (p.1, -p.2) ∈ T.source := hTs ⟨ball_subset_closedBall hp.1, mem_univ _⟩
      have hqs : q ∈ T.source := hTs ⟨sphere_subset_closedBall hq.1, mem_univ _⟩
      have heq : (p.1, -p.2) = q := T.injOn hps hqs (hpy.trans hqy.symm)
      have hx := congrArg Prod.fst heq
      have hpn : ‖p.1‖ < 1 := mem_ball_zero_iff.mp hp.1
      rw [hx] at hpn
      exact (ne_of_lt hpn) (mem_sphere_zero_iff_norm.mp hq.1)
  have hFill (t : ℝ) (ht : t ∈ Icc (-ell) (-z)) :
      Tm '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ A.closedRegion :=
    fun _ hy => ((hCuts t ht).2.symm ▸ hy).1
  have hNorthClosed : (fun q : UnitTwoSphere =>
      Tm ((P.model q).1, -z + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ⊆ A.closedRegion := by
    intro y hy
    have hys : y ∈ shared := by
      change y ∈ (fun q : UnitTwoSphere =>
        T ((P.model q).1, z - lambda * (P.model q).2)) ''
          {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
      exact hProfileImage _ ▸ hy
    rw [← A.inside_union_boundary, hAb]
    exact Or.inr (Or.inr hys)
  obtain ⟨N, hNb0, hNs0, hNt0, hNp0, hNi0, hContain, hShort0, hNcap0, hNrim0⟩ :=
    exists_saddle_contained_profile_ball P (-u) Tm hTms hTm hTminv hTmh A
      (-ell) (-z) lambda tau hl (by linarith) hlt hFill hNorthClosed
  have hNb : N.boundary = replacement ∪ shared := by
    simpa only [hProfileImage] using hNb0
  have hNsource : N.chart.source = {y : E3 |
      ((M (heightCoordinates y)).1, z - lambda * (M (heightCoordinates y)).2) ∈ T.source} := by
    rw [hNs0]
    ext y
    change ((M (heightCoordinates y)).1, -z + lambda * (M (heightCoordinates y)).2) ∈
      (heightTransportTube T negD idD).source ↔ _
    rw [heightTransportTube_mem_source T negD idD]
    change ((M (heightCoordinates y)).1, -(-z + lambda * (M (heightCoordinates y)).2)) ∈
      T.source ↔ _
    rw [show -(-z + lambda * (M (heightCoordinates y)).2) =
      z - lambda * (M (heightCoordinates y)).2 by ring]
    rfl
  have hNtarget : N.chart.target = T.target := hNt0.trans hTmt
  have hNpoint (y : E3) : N.chart y =
      T ((M (heightCoordinates y)).1, z - lambda * (M (heightCoordinates y)).2) :=
    (hNp0 y).trans (hNorthPoint y)
  have hNinv (y : E3) : N.chart.symm y = heightCoordinates.symm
      (M.symm ((T.symm y).1, (z - (T.symm y).2) / lambda)) := by
    rw [hNi0, hTmi]
    apply congrArg heightCoordinates.symm
    apply congrArg M.symm
    apply Prod.ext
    · rfl
    · change (-(T.symm y).2 - -z) / lambda = (z - (T.symm y).2) / lambda
      congr 1
      ring
  have hShort : N.closedRegion ⊆ {y : E3 | |H y - z| < tau} := by
    intro y hy
    have hh := hShort0 hy
    change |Hm y - -z| < tau at hh
    rw [show Hm y - -z = -(H y - z) by rw [hHm]; ring, abs_neg] at hh
    exact hh
  have hNcap : shared = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    simpa only [hProfileImage] using hNcap0
  have hNrim : replacement ∩ shared = rim := by
    simpa only [hProfileImage, hTmSlice] using hNrim0
  have hSharedHeight (y : E3) (hy : y ∈ shared) : H y ≤ z := by
    obtain ⟨q, hq, rfl⟩ := hy
    change H (T ((P.model q).1, z - lambda * (P.model q).2)) ≤ z
    have hsource : ((P.model q).1, z - lambda * (P.model q).2) ∈ T.source :=
      hTs (a := ((P.model q).1, z - lambda * (P.model q).2))
        ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩
    rw [hTh _ hsource]
    have hm0 : 0 ≤ (P.model q).2 := by
      change 0 ≤ P.vertical _ * (heightCoordinates (q : E3)).2
      exact mul_nonneg (P.vertical_pos _).le hq
    exact sub_le_self z (mul_nonneg hl.le hm0)
  have hRimShared : rim ⊆ shared := fun _ hy => (hNrim.symm ▸ hy).2
  have hERim : E ∩ shared = rim := by
    ext y
    constructor
    · intro hy
      have hyh : H y = z := le_antisymm (hSharedHeight y hy.2) hy.1.2
      change y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))
      exact hcircleZ.symm ▸ ⟨hy.1.1, hyh⟩
    · intro hy
      have hh : y ∈ S ∩ {y | H y = z} := hcircleZ ▸ hy
      exact ⟨⟨hh.1, hh.2.ge⟩, hRimShared hy⟩
  have hRetained : A.closedRegion ∩ R ⊆ shared := by
    rintro y ⟨hyA, hyR⟩
    have hyB : y ∈ A.boundary := by
      rcases A.inside_union_boundary.symm ▸ hyA with hy | hy
      · exact False.elim (disjoint_left.mp hAvoid hy hyR.1)
      · exact hy
    rcases hAb ▸ hyB with hyE | hyD
    · have hyh : H y = z := le_antisymm hyR.2 hyE.2
      apply hRimShared
      change y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))
      exact hcircleZ.symm ▸ ⟨hyR.1, hyh⟩
    · exact hyD
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  have hScompact : IsCompact S := by
    simpa only [image_univ] using isCompact_univ.image hj
  have hRclosed : IsClosed R := hScompact.isClosed.inter (isClosed_le H.continuous continuous_const)
  have hPatchN (q : UnitTwoSphere) (hq : -ov < (heightCoordinates (q : E3)).2) :
      N.chart (q : E3) ∈ A.boundary := by
    rw [hNpoint]
    have hh := hPatch q hq
    change Tm ((M (heightCoordinates (q : E3))).1,
      -z + lambda * (M (heightCoordinates (q : E3))).2) ∈ A.boundary at hh
    rw [hNorthPoint] at hh
    exact hh
  have hAn : A.boundary = E ∪ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNcap]
    exact hAb
  have hNn : N.boundary = replacement ∪ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNcap]
    exact hNb
  have hMeet : E ∩ N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} =
      replacement ∩ N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNcap]
    exact hERim.trans hNrim.symm
  have hAR : A.closedRegion ∩ R ⊆ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNcap]
    exact hRetained
  have hProtected : A.closedRegion ∩ (R ∪ Kcaps) ⊆ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rintro y ⟨hyA, hyR | hyK⟩
    · exact hAR ⟨hyA, hyR⟩
    · have hlo := hAlower y hyA
      have hhi := hKheight y hyK
      change H y < z - tau at hhi
      exact False.elim (by linarith only [hlo, hhi, hlt])
  obtain ⟨G, K, hGE, hGinv, hGfix0, hK, hKsub0, hKs, hKis⟩ :=
    exists_saddle_north_cap_end_transport A N ov hov (hov1.trans (by norm_num))
      hPatchN hContain E replacement (R ∪ Kcaps) (hRclosed.union hKcaps)
      hAn hNn hMeet hProtected
  have hGfixFull : ∀ y ∈ shared ∪ R ∪ Kcaps, G y = y ∧ G.symm y = y := by
    simpa only [← hNcap, union_assoc] using hGfix0
  have hGfix : ∀ y ∈ shared ∪ R, G y = y ∧ G.symm y = y :=
    fun y hy => hGfixFull y (Or.inl hy)
  have hKsub : K ⊆ (shared ∪ R ∪ Kcaps)ᶜ := by
    simpa only [← hNcap, union_assoc] using hKsub0
  have hSdecomp : S = R ∪ E := by
    ext y
    constructor
    · intro hy
      rcases le_total (H y) z with hle | hge
      · exact Or.inl ⟨hy, hle⟩
      · exact Or.inr ⟨hy, hge⟩
    · rintro (hy | hy)
      · exact hy.1
      · exact hy.1
  have hGR : G '' R = R := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [(hGfix x (Or.inr hx)).1] using hx
    · intro hy
      exact ⟨y, hy, (hGfix y (Or.inr hy)).1⟩
  have hGS : G '' S = R ∪ replacement := by
    rw [hSdecomp, image_union, hGR, hGE]
  have hGSi : G.symm '' (R ∪ replacement) = S := by
    rw [← hGS, image_image]
    simp only [G.symm_apply_apply, image_id']
  exact ⟨i, r, gamma, o, w, lambda, T, B, A, N, G, K, hsign, hunique,
    hr, hg, hgap, ho, how, hos, hw, hww, hwb, hl, hlt, hlc, hlg,
    hTsource, hTs, hT, hTi, hTh, hTih, hTold, hcentral, hcollar, hcircle',
    hBboundary, hBinside, hBclosed, hAb, hNb, hNsource, hNtarget, hNpoint, hNinv,
    hAcut, hContain, hShort, hAlower, hAvoid, hRetained, hGE, hGinv, hGfixFull,
    hK, hKsub, hKs, hKis, hGS, hGSi, hpsi.postcompose_diffeomorph G⟩

end PoincareConjecture.M25.Topology3D
