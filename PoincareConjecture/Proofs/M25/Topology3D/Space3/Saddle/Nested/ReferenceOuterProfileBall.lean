import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceOuterCanonicalBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceNorthProfileEvolution
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

set_option maxHeartbeats 800000 in

theorem exists_outer_reference_profile_ball_family :
    let C := heightCoordinates
    let I : Set ℝ := Ioo (-3 / 2) (3 / 2)
    let Jo : Set ℝ := Ioo (17 / 16 - 1 / 8192) (17 / 16 + 1 / 8192)
    let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
    let R : ℝ → ℝ → ℝ := fun t r =>
      r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
    ∃ rho : ℝ × ℝ → ℝ,
      ContDiffOn ℝ ∞ rho (I ×ˢ Jo) ∧
      (∀ p ∈ I ×ˢ Jo,
        Real.sqrt 15 / 4 < rho p ∧ rho p < Real.sqrt 4095 / 64 ∧
        R p.1 (rho p) = p.2 ∧ ∀ r ∈ Icc (rho p) 1, R p.1 r ≤ p.2) ∧
      ∃ F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
        ContDiff ℝ ∞ (fun p : E2 × ℝ => F p.2 p.1) ∧
        ContDiff ℝ ∞ (fun p : E2 × ℝ => (F p.2).symm p.1) ∧
        (∃ K : Set E2, IsCompact K ∧
          K ⊆ {v : E2 | 1 / 8 < ‖v‖ ∧ ‖v‖ < 4} ∧
          ∀ a : ℝ,
            tsupport (fun v : E2 => F a v - v) ⊆ K ∧
            tsupport (fun v : E2 => (F a).symm v - v) ⊆ K) ∧
        (∀ (a : ℝ) (v : E2), ‖v‖ ≤ 1 / 8 → F a v = v ∧ (F a).symm v = v) ∧
        (∀ a ∈ J,
          F a '' ball (0 : E2) 1 = {v : E2 | ‖v‖ < rho (v 0 / ‖v‖, a)} ∧
          F a '' closedBall (0 : E2) 1 = {v : E2 | ‖v‖ ≤ rho (v 0 / ‖v‖, a)} ∧
          F a '' sphere (0 : E2) 1 = {v : E2 | ‖v‖ = rho (v 0 / ‖v‖, a)}) ∧
        ∀ d : ℝ,
          ∃ T : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) (E2 × ℝ) E3 ∞,
            (∀ p : E2 × ℝ, T p = C.symm (F (p.2 - d) p.1, p.2)) ∧
            (∀ y : E3,
              T.symm y = ((F ((C y).2 - d)).symm (C y).1, (C y).2)) ∧
            ∀ P : SurgeryCapProfile, ∃ B0 : ℝ, 1 ≤ B0 ∧
              ∀ (h tau lambda : ℝ), |h - 17 / 16| ≤ 1 / 32768 →
                0 < tau → 0 < lambda →
                lambda * (1 + B0 + P.heightBound) < min (1 / 131072) tau →
                let s := h + d
                let Qplus : Set UnitTwoSphere := {q | 0 ≤ (C (q : E3)).2}
                let Qminus : Set UnitTwoSphere := {q | (C (q : E3)).2 ≤ 0}
                let cap : UnitTwoSphere → E3 := fun q =>
                  T ((P.model q).1, s + lambda * (P.model q).2)
                let north : Set E3 := cap '' Qplus
                let south : Set E3 := cap '' Qminus
                let rim : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
                let cyl : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ Ici s)
                let retained : Set UnitTwoSphere :=
                  {q | let p := C (q : E3)
                    p.2 ≤ 0 ∨ rho (p.1 0 / ‖p.1‖, h) ≤ ‖p.1‖}
                let E : Set E3 := (fun q : UnitTwoSphere =>
                  nestedReferenceDiffeomorph d (q : E3)) '' retained
                let M := flatCapDiffeomorph P.horizontal P.vertical
                  P.horizontal_smooth P.vertical_smooth
                  (fun z => (P.horizontal_pos z).ne')
                  (fun x => (P.vertical_pos x).ne')
                ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
                  let A := (nestedReferenceBallChart d).mapDiffeomorph G
                  A.chart.source = univ ∧ A.chart.target = univ ∧
                  (∀ y : E3, A.chart y = G (nestedReferenceDiffeomorph d y)) ∧
                  (∀ y : E3, A.chart.symm y =
                    (nestedReferenceDiffeomorph d).symm (G.symm y)) ∧
                  E ⊆ (nestedReferenceBallChart d).boundary ∩
                    {y : E3 | (C y).2 ≤ s} ∧
                  (∀ y ∈ E, G y = y ∧ G.symm y = y) ∧
                  A.boundary = E ∪ north ∧ E ∩ north = rim ∧
                  (∀ a ∈ Icc (h - 1 / 131072) h,
                    A.inside ∩ {y : E3 | (C y).2 = a + d} =
                      T '' (ball (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
                    A.closedRegion ∩ {y : E3 | (C y).2 = a + d} =
                      T '' (closedBall (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
                    A.boundary ∩ {y : E3 | (C y).2 = a + d} =
                      T '' (sphere (0 : E2) 1 ×ˢ ({a + d} : Set ℝ))) ∧
                  (∀ y ∈ A.closedRegion,
                    d - 33 / 32 ≤ (C y).2 ∧ (C y).2 ≤ s + lambda * P.heightBound) ∧
                  Disjoint A.inside cyl ∧ A.closedRegion ∩ cyl ⊆ north ∧
                  A.closedRegion ∩ {y : E3 | s ≤ (C y).2} ⊆
                    T '' (closedBall (0 : E2) 1 ×ˢ Ici s) ∧
                  ∃ N : BallNeighborhoodChart E3 E3,
                    N.chart.source = univ ∧ N.chart.target = univ ∧
                    (∀ y : E3, N.chart y =
                      T ((M (C y)).1, s + lambda * (M (C y)).2)) ∧
                    (∀ y : E3, N.chart.symm y = C.symm
                      (M.symm ((T.symm y).1, ((T.symm y).2 - s) / lambda))) ∧
                    N.boundary = south ∪ north ∧
                    N.closedRegion ⊆ A.closedRegion ∧
                    N.closedRegion ⊆ {y : E3 | |(C y).2 - s| < tau} ∧
                    north = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (C y).2} ∧
                    south ∩ north = rim ∧
                    (∀ q : UnitTwoSphere, -1 / 8 < (C (q : E3)).2 →
                      N.chart (q : E3) ∈ A.boundary) := by
  classical
  dsimp only
  let C := heightCoordinates
  obtain ⟨rho, hrho, hroots, F, hF, hFi, hFsupport, hFfix, himages, hcaps⟩ :=
    exists_outer_reference_cap_family
  refine ⟨rho, hrho, hroots, F, hF, hFi, hFsupport, hFfix, himages, ?_⟩
  intro d
  have hFshift : ContDiff ℝ ∞ (fun p : ℝ × E2 => F (p.1 - d) p.2) :=
    hF.comp (contDiff_snd.prodMk (contDiff_fst.sub contDiff_const))
  have hFishift : ContDiff ℝ ∞ (fun p : ℝ × E2 => (F (p.1 - d)).symm p.2) :=
    hFi.comp (contDiff_snd.prodMk (contDiff_fst.sub contDiff_const))
  let T := (planarFamilyGraphDiffeomorph (fun a => F (a - d)) hFshift hFishift).trans
    C.symm.toDiffeomorph
  have hT (p : E2 × ℝ) : T p = C.symm (F (p.2 - d) p.1, p.2) := rfl
  have hTi (y : E3) : T.symm y = ((F ((C y).2 - d)).symm (C y).1, (C y).2) := rfl
  have hheight (p : E2 × ℝ) : (C (T p)).2 = p.2 := by
    rw [hT, C.apply_symm_apply]
  refine ⟨T, hT, hTi, ?_⟩
  intro P
  obtain ⟨B0, hB0, hevolution⟩ := exists_north_profile_evolution_in_height_strip P
  refine ⟨B0, hB0, ?_⟩
  intro h tau lambda hh htau hlambda hsmall
  have hbeta : lambda * (1 + B0 + P.heightBound) < 1 / 131072 :=
    hsmall.trans_le (min_le_left _ _)
  have htau' : lambda * (1 + B0 + P.heightBound) < tau :=
    hsmall.trans_le (min_le_right _ _)
  have hlSmall : lambda < 1 / 131072 := by
    have hm := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 1 + B0 + P.heightBound by linarith [P.one_le_heightBound])
      hlambda.le
    simpa only [mul_one] using hm.trans_lt hbeta
  have hBsmall : lambda * B0 < 1 / 131072 :=
    (mul_le_mul_of_nonneg_left (by linarith [P.one_le_heightBound]) hlambda.le).trans_lt hbeta
  have hMsmall : lambda * P.heightBound < 1 / 131072 :=
    (mul_le_mul_of_nonneg_left (by linarith only [hB0]) hlambda.le).trans_lt hbeta
  have hMshort : lambda * P.heightBound < tau :=
    (mul_le_mul_of_nonneg_left (by linarith only [hB0]) hlambda.le).trans_lt htau'
  let s := h + d
  let Qplus : Set UnitTwoSphere := {q | 0 ≤ (C (q : E3)).2}
  let Qminus : Set UnitTwoSphere := {q | (C (q : E3)).2 ≤ 0}
  let cap : UnitTwoSphere → E3 := fun q =>
    T ((P.model q).1, s + lambda * (P.model q).2)
  let north := cap '' Qplus
  let south := cap '' Qminus
  let rim : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
  let cyl : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ Ici s)
  let retained : Set UnitTwoSphere :=
    {q | (C (q : E3)).2 ≤ 0 ∨ rho ((C (q : E3)).1 0 / ‖(C (q : E3)).1‖, h) ≤
      ‖(C (q : E3)).1‖}
  let E : Set E3 := (fun q : UnitTwoSphere =>
    nestedReferenceDiffeomorph d (q : E3)) '' retained
  let Mc := stackCapProfilePath
    (stackCanonicalHorizontal (1 / 4) (1 / 2)) (stackCanonicalHorizontal (1 / 4) (1 / 2))
    (stackCanonicalVertical (1 / 4) (1 / 2)) (stackCanonicalVertical (1 / 4) (1 / 2)) 0
  let cap0 : UnitTwoSphere → E3 := fun q =>
    let m := Mc (C (q : E3))
    T (m.1, s + lambda * m.2)
  let capc : UnitTwoSphere → E3 := fun q =>
    let m := Mc (C (q : E3))
    C.symm (F (h + lambda * m.2) m.1, h + lambda * m.2 + d)
  have hroot (theta : ℝ) (ht : theta ∈ Ioo (-3 / 2 : ℝ) (3 / 2))
      (a : ℝ) (ha : a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384)) :
      Real.sqrt 15 / 4 < rho (theta, a) ∧
      rho (theta, a) < Real.sqrt 4095 / 64 ∧
      rho (theta, a) ^ 2 + Real.sqrt (1 - rho (theta, a) ^ 2) +
        rho (theta, a) * theta / 32 = a := by
    have hp := hroots (theta, a) ⟨ht, ⟨by linarith only [ha.1], by linarith only [ha.2]⟩⟩
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  obtain ⟨V, g, D, _hV, _hBV, _hgs, _hBrad, hgraph, hg, hgstrict, hD, hDc,
      hDsupp, hDgraph⟩ := hcaps h lambda hh hlambda hlSmall
  obtain ⟨Tc, hTc, _hTci, hcapc, Phi, _hPhic, _hPhiic, _hPhiH,
      _hA0s, _hA0t, _hA0f, _hA0i, hEdata, hG0fix, hBoundary0, hRim0,
      _hRetained0, _hPatch0, hCuts0⟩ :=
    exists_outer_reference_canonical_ball rho F hF hFi hroot himages
      h lambda d hh hlambda hlSmall g D hD hDc hDsupp hDgraph hg hgstrict hgraph
  have hTeq : Tc = T := by
    apply Diffeomorph.ext
    intro p
    exact (hTc p).trans (hT p).symm
  subst Tc
  let G0 := C.toDiffeomorph.trans (Phi.trans C.symm.toDiffeomorph)
  let A0 := (nestedReferenceBallChart d).mapDiffeomorph G0
  change E ⊆ (nestedReferenceBallChart d).boundary ∩ {y : E3 | (C y).2 ≤ s} at hEdata
  change ∀ y ∈ E, G0 y = y ∧ G0.symm y = y at hG0fix
  change ∀ q : UnitTwoSphere, capc q = cap0 q at hcapc
  change A0.boundary = E ∪ capc '' Qplus at hBoundary0
  change E ∩ (capc '' Qplus) = rim at hRim0
  have hcc : capc = cap0 := funext hcapc
  rw [hcc] at hBoundary0 hRim0
  obtain ⟨O, Psi, K, _hO, _hrim, _hPsis, _hPsiis, _hzero, _hpoint,
      hcapImage, _hcapInverse, _hK, _hKs, _hsupp, _hisupp, _hfixK, _hfixO, hfixLower⟩ :=
    hevolution T s lambda (1 / 131072) hheight hlambda (by norm_num) hBsmall
  change Psi 1 '' (cap0 '' Qplus) = north at hcapImage
  let G := G0.trans (Psi 1)
  let A := (nestedReferenceBallChart d).mapDiffeomorph G
  have hEi (y : E3) (hy : y ∈ E) : Psi 1 y = y ∧ (Psi 1).symm y = y :=
    hfixLower 1 y (hEdata hy).2
  have hGfix (y : E3) (hy : y ∈ E) : G y = y ∧ G.symm y = y := by
    change Psi 1 (G0 y) = y ∧ G0.symm ((Psi 1).symm y) = y
    exact ⟨by rw [(hG0fix y hy).1]; exact (hEi y hy).1,
      by rw [(hEi y hy).2]; exact (hG0fix y hy).2⟩
  have hImageE : Psi 1 '' E = E := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [(hEi x hx).1]
      exact hx
    · exact fun hy => ⟨y, hy, (hEi y hy).1⟩
  have hAi : A.inside = Psi 1 '' A0.inside :=
    image_comp (Psi 1) (fun y => G0 (nestedReferenceDiffeomorph d y)) (ball 0 1)
  have hAc : A.closedRegion = Psi 1 '' A0.closedRegion :=
    image_comp (Psi 1) (fun y => G0 (nestedReferenceDiffeomorph d y)) (closedBall 0 1)
  have hAb : A.boundary = Psi 1 '' A0.boundary :=
    image_comp (Psi 1) (fun y => G0 (nestedReferenceDiffeomorph d y)) (sphere 0 1)
  have hBoundary : A.boundary = E ∪ north := by
    rw [hAb, hBoundary0, image_union, hImageE, hcapImage]
  have hRim : E ∩ north = rim := by
    ext y
    constructor
    · rintro ⟨hyE, hyN⟩
      rw [← hcapImage] at hyN
      obtain ⟨x, hx, hxy⟩ := hyN
      have he : x = y := (Psi 1).injective (hxy.trans (hEi y hyE).1.symm)
      subst x
      exact hRim0 ▸ ⟨hyE, hx⟩
    · intro hy
      have hy' : y ∈ E ∩ (cap0 '' Qplus) := hRim0.symm ▸ hy
      refine ⟨hy'.1, ?_⟩
      rw [← hcapImage]
      exact ⟨y, hy'.2, (hEi y hy'.1).1⟩
  have hPlane (S : Set E3) (a : ℝ) (ha : a ≤ h) :
      (Psi 1 '' S) ∩ {y : E3 | (C y).2 = a + d} =
        S ∩ {y : E3 | (C y).2 = a + d} := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, hxy⟩, hyh⟩
      have hyle : (C y).2 ≤ s := by change (C y).2 = a + d at hyh; dsimp [s]; linarith
      have he : x = y := (Psi 1).injective (hxy.trans (hfixLower 1 y hyle).1.symm)
      subst x
      exact ⟨hx, hyh⟩
    · rintro ⟨hy, hyh⟩
      have hyle : (C y).2 ≤ s := by change (C y).2 = a + d at hyh; dsimp [s]; linarith
      exact ⟨⟨y, hy, (hfixLower 1 y hyle).1⟩, hyh⟩
  have hCuts (a : ℝ) (ha : a ∈ Icc (h - 1 / 131072) h) :
      A.inside ∩ {y : E3 | (C y).2 = a + d} =
        T '' (ball (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
      A.closedRegion ∩ {y : E3 | (C y).2 = a + d} =
        T '' (closedBall (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
      A.boundary ∩ {y : E3 | (C y).2 = a + d} =
        T '' (sphere (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hAi, hPlane A0.inside a ha.2]
      exact (hCuts0 a ha).1
    · rw [hAc, hPlane A0.closedRegion a ha.2]
      exact (hCuts0 a ha).2.1
    · rw [hAb, hPlane A0.boundary a ha.2]
      exact (hCuts0 a ha).2.2
  have hInsideClosed : A.inside ⊆ A.closedRegion := by
    rw [← A.inside_union_boundary]
    exact subset_union_left
  have hBoundaryClosed : A.boundary ⊆ A.closedRegion := by
    rw [← A.inside_union_boundary]
    exact subset_union_right
  have hv : ‖C.symm ((0 : E2), (1 : ℝ))‖ = 1 := by
    have hh' := heightCoordinates_symm_norm_sq ((0 : E2), (1 : ℝ))
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), one_pow, zero_add] at hh'
    nlinarith [norm_nonneg (C.symm ((0 : E2), (1 : ℝ)))]
  let u : UnitTwoSphere := ⟨C.symm (0, 1), mem_sphere_zero_iff_norm.mpr hv⟩
  have hu (y : E3) : inner ℝ (u : E3) y = (C y).2 := by
    change inner ℝ (heightCoordinates.symm ((0 : E2), (1 : ℝ))) y =
      (heightCoordinates y).2
    simp only [heightCoordinates_symm_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_three, heightCoordinates_snd_apply]
    simp
  let Tp := T.toHomeomorph.toOpenPartialHomeomorph
  have hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ Tp.source := fun p _ => mem_univ p
  have hfilled (t : ℝ) (ht : t ∈ Icc (s - 1 / 131072) s) :
      Tp '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ A.closedRegion := by
    have ha : t - d ∈ Icc (h - 1 / 131072) h := by
      dsimp only [s] at ht
      constructor <;> linarith only [ht.1, ht.2]
    have hc := (hCuts (t - d) ha).2.1
    rw [sub_add_cancel] at hc
    change T '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ A.closedRegion
    rw [← hc]
    exact inter_subset_left
  have hnorth : north ⊆ A.closedRegion :=
    fun y hy => hBoundaryClosed (hBoundary.symm ▸ Or.inr hy)
  obtain ⟨N, hNb, hNs, hNt, hNf, hNi, hNc, hNh, hNnorth, hNmeet⟩ :=
    exists_saddle_contained_profile_ball P u Tp hsource
      T.contMDiff_toFun.contDiff.contDiffOn T.contMDiff_invFun.contDiff.contDiffOn
      (fun p _ => (hu (Tp p)).trans (hheight p)) A (s - 1 / 131072) s lambda tau
      hlambda (by linarith only [hMsmall]) hMshort hfilled hnorth
  have hNsource : N.chart.source = univ := by
    rw [hNs]
    ext y
    simp [Tp]
  have hNtarget : N.chart.target = univ := by rw [hNt]; rfl
  have hNheight : N.closedRegion ⊆ {y : E3 | |(C y).2 - s| < tau} := by
    intro y hy
    have hh' := hNh hy
    change |inner ℝ (u : E3) y - s| < tau at hh'
    rwa [hu] at hh'
  have hNpoint (q : UnitTwoSphere) : N.chart (q : E3) = cap q := hNf q
  have hPatch (q : UnitTwoSphere) (hq : -1 / 8 < (C (q : E3)).2) :
      N.chart (q : E3) ∈ A.boundary := by
    rw [hNpoint]
    by_cases hp : 0 ≤ (C (q : E3)).2
    · exact hBoundary.symm ▸ Or.inr ⟨q, hp, rfl⟩
    · have hw : (C (q : E3)).2 < 0 := lt_of_not_ge hp
      have habs : |(C (q : E3)).2| ≤ 1 / 4 := by rw [abs_of_neg hw]; linarith
      have hm := surgeryCapModel_cylinder P.horizontal P.vertical
        P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        P.horizontal_near P.vertical_far q habs
      change P.model q = ((circleDirection (C (q : E3)).1 : E2), (C (q : E3)).2) at hm
      have hmn : ‖(P.model q).1‖ = 1 := by rw [hm]; exact norm_eq_of_mem_sphere _
      let a := h + lambda * (C (q : E3)).2
      have ha : a ∈ Icc (h - 1 / 131072) h := by
        have hlo := mul_lt_mul_of_pos_left hq hlambda
        have hhi := mul_neg_of_pos_of_neg hlambda hw
        constructor <;> dsimp only [a] <;> nlinarith only [hlo, hhi, hlSmall]
      have hi : cap q ∈ A.boundary ∩ {y : E3 | (C y).2 = a + d} := by
        rw [(hCuts a ha).2.2]
        refine ⟨((P.model q).1, s + lambda * (P.model q).2), ⟨?_, ?_⟩, rfl⟩
        · exact mem_sphere_zero_iff_norm.mpr hmn
        · change s + lambda * (P.model q).2 = a + d
          rw [hm]
          dsimp only [s, a]
          ring
      exact hi.1
  have hNorthHeight (y : E3) (hy : y ∈ north) :
      s ≤ (C y).2 ∧ (C y).2 ≤ s + lambda * P.heightBound := by
    obtain ⟨q, hq, rfl⟩ := hy
    change s ≤ (C (T _)).2 ∧ (C (T _)).2 ≤ s + lambda * P.heightBound
    rw [hheight]
    have hm0 : 0 ≤ (P.model q).2 := by
      change 0 ≤ P.vertical _ * (C (q : E3)).2
      exact mul_nonneg (P.vertical_pos _).le hq
    have hm1 := (abs_le.mp (P.height_bound q)).2
    change (P.model q).2 ≤ P.heightBound at hm1
    exact ⟨by nlinarith only [hlambda, hm0], by nlinarith only [hlambda, hm1]⟩
  have hElo (y : E3) (hy : y ∈ E) : d - 33 / 32 ≤ (C y).2 := by
    obtain ⟨q, _hq, rfl⟩ := hy
    have hq := sphere_height_coordinates_sq q
    have hn : ‖(C (q : E3)).1‖ ^ 2 =
        ((C (q : E3)).1 0) ^ 2 + ((C (q : E3)).1 1) ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hw : -1 ≤ (C (q : E3)).2 := by nlinarith only [hq, sq_nonneg ‖(C (q : E3)).1‖]
    have hx : -1 ≤ (C (q : E3)).1 0 := by
      nlinarith only [hq, hn, sq_nonneg ((C (q : E3)).1 1), sq_nonneg (C (q : E3)).2]
    have he : (C (nestedReferenceDiffeomorph d (q : E3))).2 =
        (C (q : E3)).2 + ‖(C (q : E3)).1‖ ^ 2 + (C (q : E3)).1 0 / 32 + d := by
      rw [(nestedReferenceDiffeomorph_apply_symm d).1, hn]
      change (q : E3) 2 + (q : E3) 0 ^ 2 + (q : E3) 1 ^ 2 + (q : E3) 0 / 32 + d =
        (q : E3) 2 + ((q : E3) 0 ^ 2 + (q : E3) 1 ^ 2) + (q : E3) 0 / 32 + d
      ring
    rw [he]
    nlinarith only [hw, hx, sq_nonneg ‖(C (q : E3)).1‖]
  have hBoundaryHeight (y : E3) (hy : y ∈ A.boundary) :
      d - 33 / 32 ≤ (C y).2 ∧ (C y).2 ≤ s + lambda * P.heightBound := by
    rw [hBoundary] at hy
    have hslo : d - 33 / 32 ≤ s := by dsimp only [s]; linarith [(abs_le.mp hh).1]
    have hMpos := P.one_le_heightBound
    rcases hy with hy | hy
    · exact ⟨hElo y hy, by
        have hehi := (hEdata hy).2
        change (C y).2 ≤ s at hehi
        nlinarith only [hehi, hlambda, hMpos]⟩
    · exact ⟨hslo.trans (hNorthHeight y hy).1, (hNorthHeight y hy).2⟩
  have hHeightMax (sigma bound : ℝ) (hsigma : |sigma| = 1)
      (hbd : ∀ y ∈ A.boundary, sigma * (C y).2 ≤ bound) :
      ∀ y ∈ A.closedRegion, sigma * (C y).2 ≤ bound := by
    have hne : A.closedRegion.Nonempty := ⟨A.chart 0, 0, by simp, rfl⟩
    obtain ⟨y, hy, hmax⟩ := A.closedRegion_compact.exists_isMaxOn hne
      (f := fun y : E3 => sigma * (C y).2) (by fun_prop)
    have hyb : y ∈ A.boundary := by
      have hpart : y ∈ A.inside ∪ A.boundary := A.inside_union_boundary.symm ▸ hy
      rcases hpart with hi | hb
      · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp A.inside_open y hi
        let y' := y + (sigma * (r / 2)) • (u : E3)
        have hyn : y' ∈ A.closedRegion := hInsideClosed (hball (by
          rw [mem_ball, dist_eq_norm]
          change ‖y + (sigma * (r / 2)) • (u : E3) - y‖ < r
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere u,
            mul_one, abs_mul, hsigma, one_mul, abs_of_pos (by positivity : 0 < r / 2)]
          linarith))
        have he : (C y').2 = (C y).2 + sigma * (r / 2) := by
          change (C (y + (sigma * (r / 2)) • C.symm (0, 1))).2 = _
          rw [map_add, map_smul, C.apply_symm_apply]
          simp
        have hs2 : sigma ^ 2 = 1 := by nlinarith only [sq_abs sigma, hsigma]
        have hb' : sigma * (C y').2 ≤ sigma * (C y).2 := hmax hyn
        rw [he, mul_add, ← mul_assoc, ← pow_two, hs2, one_mul] at hb'
        linarith only [hb', hr]
      · exact hb
    exact fun x hx => (hmax hx).trans (hbd y hyb)
  have hHeight (y : E3) (hy : y ∈ A.closedRegion) :
      d - 33 / 32 ≤ (C y).2 ∧ (C y).2 ≤ s + lambda * P.heightBound := by
    have hlo := hHeightMax (-1) (-(d - 33 / 32)) (by norm_num)
      (fun z hz => by linarith only [(hBoundaryHeight z hz).1]) y hy
    have hhi := hHeightMax 1 (s + lambda * P.heightBound) (by norm_num)
      (fun z hz => by simpa only [one_mul] using (hBoundaryHeight z hz).2) y hy
    constructor <;> linarith only [hlo, hhi]
  have hExterior (x : E2) (hx : 1 < ‖x‖) (z : ℝ) (hz : s < z) :
      T (x, z) ∉ A.closedRegion := by
    let Y : Set E3 := (fun a : ℝ => T (x, a)) '' Ioi s
    have hc : IsPreconnected Y := isPreconnected_Ioi.image _
      (T.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hd : Disjoint Y A.boundary := by
      apply Set.disjoint_left.mpr
      rintro y ⟨a, ha, rfl⟩ hb
      rw [hBoundary] at hb
      rcases hb with hb | hb
      · have hehi := (hEdata hb).2
        change (C (T (x, a))).2 ≤ s at hehi
        rw [hheight] at hehi
        exact (not_lt_of_ge hehi) ha
      · obtain ⟨q, _hq, he⟩ := hb
        have hxy := congrArg Prod.fst (T.injective he)
        have hn := P.model_fst_norm_le q
        change (P.model q).1 = x at hxy
        rw [hxy] at hn
        exact (not_lt_of_ge hn) hx
    rcases A.preconnected_subset_inside_or_outside hc hd with hi | ho
    · have hpoint : T (x, s + lambda * P.heightBound + 1) ∈ Y :=
        ⟨s + lambda * P.heightBound + 1, by
          change s < s + lambda * P.heightBound + 1
          nlinarith [P.one_le_heightBound], rfl⟩
      have hb := (hHeight _ (hInsideClosed (hi hpoint))).2
      rw [hheight] at hb
      linarith
    · exact ho ⟨z, hz, rfl⟩
  have hCylinder (x : E2) (hx : ‖x‖ = 1) (z : ℝ) (hz : s ≤ z) :
      T (x, z) ∉ A.inside := by
    have hc : Continuous (fun e : ℝ => T ((1 + e) • x, z + e)) := by fun_prop
    have ht : Tendsto (fun e : ℝ => T ((1 + e) • x, z + e)) (𝓝[>] (0 : ℝ))
        (𝓝 (T (x, z))) := by
      have ht0 : Tendsto (fun e : ℝ => T ((1 + e) • x, z + e)) (𝓝 (0 : ℝ))
          (𝓝 (T ((1 + (0 : ℝ)) • x, z + (0 : ℝ)))) := hc.continuousAt.tendsto
      simpa only [add_zero, one_smul] using
        ht0.mono_left nhdsWithin_le_nhds
    apply A.inside_open.isClosed_compl.mem_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with e he
    have he0 : 0 < e := he
    have hn : 1 < ‖(1 + e) • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hx, mul_one]
      linarith
    exact fun hi => hExterior _ hn _ (by linarith) (hInsideClosed hi)
  have hDisjoint : Disjoint A.inside cyl := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    exact hCylinder x (mem_sphere_zero_iff_norm.mp hx) z hz hy
  have hCylinderMeet : A.closedRegion ∩ cyl ⊆ north := by
    rintro y ⟨hy, ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩⟩
    have hn := hCylinder x (mem_sphere_zero_iff_norm.mp hx) z hz
    have hb : T (x, z) ∈ A.boundary := by
      rw [← A.inside_union_boundary] at hy
      exact hy.resolve_left hn
    rw [hBoundary] at hb
    rcases hb with he | hn
    · have hle := (hEdata he).2
      change (C (T (x, z))).2 ≤ s at hle
      rw [hheight] at hle
      have heq : z = s := le_antisymm hle hz
      have hri : T (x, z) ∈ rim := ⟨(x, z), ⟨hx, heq⟩, rfl⟩
      exact (show T (x, z) ∈ E ∩ north from hRim.symm ▸ hri).2
    · exact hn
  have hUpperSolid : A.closedRegion ∩ {y : E3 | s ≤ (C y).2} ⊆
      T '' (closedBall (0 : E2) 1 ×ˢ Ici s) := by
    rintro y ⟨hy, hz⟩
    have hiy : (T.symm y).2 = (C y).2 := by rw [hTi]
    have hn : ‖(T.symm y).1‖ ≤ 1 := by
      by_cases he : (C y).2 = s
      · have hm : y ∈ T '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) :=
          (hCuts h ⟨by linarith, le_rfl⟩).2.1 ▸ ⟨hy, he⟩
        obtain ⟨p, hp, rfl⟩ := hm
        rw [T.symm_apply_apply]
        exact mem_closedBall_zero_iff.mp hp.1
      · have hs : s < (T.symm y).2 := by rw [hiy]; exact lt_of_le_of_ne hz (Ne.symm he)
        by_contra hh'
        have hx := lt_of_not_ge hh'
        have ho := hExterior (T.symm y).1 hx (T.symm y).2 hs
        rw [Prod.eta, T.apply_symm_apply] at ho
        exact ho hy
    exact ⟨T.symm y, ⟨mem_closedBall_zero_iff.mpr hn, hiy.symm ▸ hz⟩,
      T.apply_symm_apply y⟩
  refine ⟨G, ?_, ?_, fun _ => rfl, fun _ => rfl, hEdata, hGfix, hBoundary,
    hRim, hCuts, hHeight, hDisjoint, hCylinderMeet, hUpperSolid,
    N, hNsource, hNtarget, hNf, hNi, hNb, hNc, hNheight, hNnorth, hNmeet, hPatch⟩
  · ext y
    simp [G, BallNeighborhoodChart.mapDiffeomorph, nestedReferenceBallChart]
  · ext y
    simp [G, BallNeighborhoodChart.mapDiffeomorph, nestedReferenceBallChart]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
