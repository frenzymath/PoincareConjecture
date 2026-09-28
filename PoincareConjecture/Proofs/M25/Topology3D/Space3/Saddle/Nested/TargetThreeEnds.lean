import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleLowerLevelBand
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerCutMotion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.StaggeredLowerEnds
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.UpperEnd
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_saddle_nested_target_three_ends
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (i o : Fin 2) (hio : i ≠ o)
    (hnested : (W.disc i).closedRegion ⊆ (W.disc o).inside)
    (P : SurgeryCapProfile) (z v tau : ℝ)
    (hz : W.level < z)
    (hzc : z < ⟪(u : E3), psi (D.point, 0)⟫_ℝ)
    (hcv : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < v)
    (hseams : ∀ k : Fin D.capCount, (D.cap k).sign = -1 →
      v < (D.cap k).cutHeight + (D.cap k).sign * (D.cap k).removal)
    (hlevel : IsConnected
      {q : UnitTwoSphere | ⟪(u : E3), psi (q, 0)⟫_ℝ = v})
    (htau : 0 < tau) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (psi (D.point, 0))
    let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
    ∃ tgap : ℝ, 0 < tgap ∧ tgap < tau ∧
      ∀ t : ℝ, z - tgap < t → t < z →
      let cut : Fin 3 → ℝ := ![z, t, v]
      let sign : Fin 3 → ℝ := ![1, 1, -1]
      ∃ (b : ℝ) (T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3),
        0 < b ∧ 4 * b < tau ∧ 4 * b < z - t ∧ 4 * b < c - z ∧ 4 * b < v - c ∧
        (∀ k : Fin 3,
          closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T k).source ∧
          ContDiffOn ℝ ∞ (T k) (T k).source ∧
          ContDiffOn ℝ ∞ (T k).symm (T k).target ∧
          (∀ x ∈ (T k).source, H (T k x) = x.2) ∧
          (∀ y ∈ (T k).target, ((T k).symm y).2 = H y)) ∧
        (∀ s ∈ Icc (t - 4 * b) (z + 4 * b),
          S ∩ {y : E3 | H y = s} =
            T 0 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
              T 1 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
          T 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
            T 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ))) ∧
        (∀ s ∈ Icc (v - 4 * b) (v + 4 * b),
          T 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
            S ∩ {y : E3 | H y = s}) ∧
        ∀ lambda : Fin 3 → ℝ, (∀ k, 0 < lambda k) →
          (∀ k, lambda k * P.heightBound < b) →
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          let cap : Fin 3 → Set E3 := fun k =>
            P.capMap (T k) (cut k) (sign k) 0 (lambda k) '' Qminus
          let Lcyl : Set E3 := T 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)
          let M : Set E3 := (S ∩ {y | z ≤ H y ∧ H y ≤ v}) ∪ Lcyl
          ∃ G : D3,
            G '' S = M ∪ ⋃ k : Fin 3, cap k ∧
            G.symm '' (M ∪ ⋃ k : Fin 3, cap k) = S ∧
            (∀ y ∈ M, G y = y ∧ G.symm y = y) ∧
            (∀ (k : Fin 3) (y : E3), y ∈ cap k →
              |H y - cut k| ≤ lambda k * P.heightBound) := by
  classical
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (psi (D.point, 0))
  let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
  let m := W.level
  let ell : Fin 2 → ℝ := fun k =>
    (D.cap (W.label k)).cutHeight + (D.cap (W.label k)).removal
  change z < c at hzc
  change c < v at hcv
  have hell (k : Fin 2) : ell k < m := by
    simpa only [ell, W.label_lower k, one_mul] using
      W.lower_seams_lt_level (W.label k) (W.label_lower k)
  have hlabels (k : Fin 2) : k = i ∨ k = o := by omega
  have hdata (k : Fin 2) : ∃ (gamma : ℝ)
      (U : OpenPartialHomeomorph (E2 × ℝ) E3),
      0 < gamma ∧ gamma < (m - ell k) / 8 ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ U.source ∧
      ContDiffOn ℝ ∞ U U.source ∧ ContDiffOn ℝ ∞ U.symm U.target ∧
      (∀ p ∈ U.source, H (U p) = p.2) ∧
      (∀ y ∈ U.target, (U.symm y).2 = H y) ∧
      (∀ s ∈ Icc (ell k) (m + gamma),
        U '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
          range (fun q : UnitCircle => psi (W.leg k (q, s), 0))) ∧
      U '' (ball (0 : E2) 1 ×ˢ ({m} : Set ℝ)) =
        (fun x : E2 => (heightPlaneCoordinates u).symm (x, m)) '' (W.disc k).inside ∧
      U '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) =
        (fun x : E2 => (heightPlaneCoordinates u).symm (x, m)) '' (W.disc k).closedRegion ∧
      (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 0 →
        U (((D.cap (W.label k)).profile.model q).1,
          ell k + (D.cap (W.label k)).scale * ((D.cap (W.label k)).profile.model q).2) =
            psi ((D.cap (W.label k)).sourceChart q, 0)) := by
    obtain ⟨r, gamma, ov, w, U, phase, _, hg, hgap, hov, _, _, _, _, _, _,
      hs, hU, hUi, hh, hih, _, _, _, _, _, hc, hb, hd, hold, _, _⟩ :=
      exists_saddle_lower_end_tube hP psi hpsi u D W k
    refine ⟨gamma, U, hg, hgap, hs, hU, hUi, hh, hih, hc, hb, hd, ?_⟩
    intro q hq
    have heq := hold q (lt_of_le_of_lt hq hov)
    simpa only [SurgeryCapProfile.capMap_apply, W.label_lower k, one_mul,
      add_assoc, ell] using heq.symm
  choose gamma U hg hgap hs hU hUi hh hih hcircle hball hdisc hold using hdata
  let r0 := min (gamma 0) (gamma 1) / 2
  have hr0 : 0 < r0 := div_pos (lt_min (hg 0) (hg 1)) (by norm_num)
  have hr (k : Fin 2) : r0 < gamma k := by
    have ha := min_le_left (gamma 0) (gamma 1)
    have hb := min_le_right (gamma 0) (gamma 1)
    fin_cases k <;> dsimp [r0] <;> linarith [hg 0, hg 1]
  have hcircle0 (k : Fin 2) (s : ℝ) (hzs : s ∈ Icc (m - r0) (m + r0)) :
      U k '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
        range (fun q : UnitCircle => psi (W.leg k (q, s), 0)) := by
    apply hcircle k s
    exact ⟨by linarith [hgap k, hr k, hzs.1], by linarith [hr k, hzs.2]⟩
  obtain ⟨dcov, hdcov, hdcovr, hcov⟩ :=
    W.exists_physical_level_band psi hpsi u D U r0 hr0 hcircle0
  let O := U o '' (ball (0 : E2) 1 ×ˢ (univ : Set ℝ))
  have hO : IsOpen O := (U o).isOpen_image_of_subset_source
    (isOpen_ball.prod isOpen_univ) (fun p hp => hs o ⟨ball_subset_closedBall hp.1, hp.2⟩)
  have hcompact : IsCompact (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) :=
    (isCompact_closedBall (0 : E2) 1).prod isCompact_singleton
  have hbase : closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ) ⊆
      (U i).source ∩ U i ⁻¹' O := by
    intro p hp
    refine ⟨hs i ⟨hp.1, mem_univ _⟩, ?_⟩
    have hpimage : U i p ∈ U i '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) :=
      ⟨p, hp, rfl⟩
    rw [hdisc i] at hpimage
    have hout : U i p ∈ U o '' (ball (0 : E2) 1 ×ˢ ({m} : Set ℝ)) := by
      rw [hball o]
      exact image_mono hnested hpimage
    exact image_mono (prod_mono_right (subset_univ _)) hout
  obtain ⟨q, hq, hthick⟩ :=
    hcompact.exists_thickening_subset_open ((U i).isOpen_inter_preimage hO) hbase
  let delta := min dcov (q / 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelcov : delta ≤ dcov := min_le_left _ _
  have hdelq : delta ≤ q / 2 := min_le_right _ _
  have hdelseam (k : Fin 2) : delta < m - ell k := by
    linarith [hr k, hgap k, hg k]
  have hnest (s : ℝ) (hsd : |s - m| ≤ delta) :
      U i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
        U o '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
    rintro y ⟨⟨x, r⟩, ⟨hx, hrmem⟩, rfl⟩
    have hrs : r = s := mem_singleton_iff.mp hrmem
    subst r
    have hv := hthick (mem_thickening_iff.mpr
      ⟨(x, m), ⟨hx, mem_singleton _⟩, by
        rw [dist_prod_same_left, Real.dist_eq]
        linarith⟩)
    obtain ⟨⟨x', r'⟩, hp, heq⟩ := hv.2
    have heqh : r' = s := by
      have heqH := congrArg H heq
      rw [hh o _ (hs o ⟨ball_subset_closedBall hp.1, hp.2⟩), hh i _ hv.1] at heqH
      exact heqH
    exact ⟨(x', r'), ⟨hp.1, mem_singleton_iff.mpr heqh⟩, heq⟩
  have hlevels (s : ℝ) (hsd : |s - m| ≤ delta) :
      S ∩ {y : E3 | H y = s} =
        U i '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
          U o '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
    have hsband : s ∈ Icc (m - dcov) (m + dcov) := by
      have hb := abs_le.mp hsd
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    ext y
    constructor
    · rintro ⟨hy, hys⟩
      obtain ⟨k, hk⟩ := hcov y hy (by change H y ∈ _; rw [hys]; exact hsband)
      change y ∈ U k '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)) at hk
      rw [hys] at hk
      rcases hlabels k with rfl | rfl
      · exact Or.inl hk
      · exact Or.inr hk
    · intro hy
      have hsub (k : Fin 2) (hk : y ∈ U k '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))) :
          y ∈ S ∩ {y : E3 | H y = s} := by
        have hsband0 : s ∈ Icc (m - r0) (m + r0) :=
          ⟨by linarith [hsband.1], by linarith [hsband.2]⟩
        have hyS : y ∈ S := by
          obtain ⟨theta, heq⟩ := (hcircle0 k s hsband0) ▸ hk
          exact ⟨W.leg k (theta, s), heq⟩
        obtain ⟨p, hp, rfl⟩ := hk
        exact ⟨hyS, (hh k p (hs k ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)).trans
          (mem_singleton_iff.mp hp.2)⟩
      exact hy.elim (hsub i) (hsub o)
  obtain ⟨e, g, K, carrier, he, _, _, _, _, _, _, _, hmono, _, _, hKH,
    _, hKS, _, _, _, _, _, haff, hKsets⟩ :=
    exists_saddle_lower_cut_motion psi hpsi u D W (max (ell 0) (ell 1)) z
      (max_lt (hell 0) (hell 1)) hz hzc
  let g1 := g 1
  let K1 := K 1
  obtain ⟨ku, gu, Up, _, _, hgu, hgugap, hUps, hUp, hUpi, hUph, hUpih,
    _, _, hUpcircle, hUpper⟩ :=
    exists_saddle_upper_end_with_later_scales psi hpsi u D v hcv hseams hlevel
  let gap := min tau (min e delta) / 4
  have hmin : 0 < min tau (min e delta) := lt_min htau (lt_min he hdelta)
  have hgap0 : 0 < gap := by dsimp [gap]; positivity
  have hgapTau : gap < tau := by
    have hm := min_le_left tau (min e delta)
    dsimp [gap]
    linarith
  refine ⟨gap, hgap0, hgapTau, ?_⟩
  intro t htg htz
  let a := z - t
  have ha : 0 < a := sub_pos.mpr htz
  have hagap : a < gap := by dsimp [a]; linarith
  have hae : a < e / 4 := by
    have hm := (min_le_right tau (min e delta)).trans (min_le_left e delta)
    dsimp [gap] at hagap
    linarith
  have hadel : a < delta / 4 := by
    have hm := (min_le_right tau (min e delta)).trans (min_le_right e delta)
    dsimp [gap] at hagap
    linarith
  have haell : a < m - ell o := by linarith [hdelseam o]
  obtain ⟨dl, hdl, _, _, hLower⟩ :=
    exists_saddle_nested_staggered_lower_ends psi hpsi u D W i o hio hnested P a (a / 16)
      ha haell (by positivity) (by linarith) U gamma hg hs hU hUi hh hold hcircle hdisc
  let B := min tau (min a (min (c - z) (min (v - c) (min gu
    (min (delta - a) (min (e - a) (min dl (min (a / 8) (m - a - ell o)))))))))
  have hB : 0 < B := by
    dsimp [B]
    exact lt_min htau (lt_min ha (lt_min (sub_pos.mpr hzc) (lt_min (sub_pos.mpr hcv)
      (lt_min hgu (lt_min (by linarith) (lt_min (by linarith)
        (lt_min hdl (lt_min (by positivity) (by linarith)))))))))
  let b := B / 16
  have hb : 0 < b := by dsimp [b]; positivity
  have hsmall : 4 * b < B := by dsimp [b]; linarith
  have hbds : 4 * b < tau ∧ 4 * b < a ∧ 4 * b < c - z ∧ 4 * b < v - c ∧
      4 * b < gu ∧ 4 * b < delta - a ∧ 4 * b < e - a ∧ 4 * b < dl ∧
      4 * b < a / 8 ∧ 4 * b < m - a - ell o := by
    simpa only [B, lt_min_iff] using hsmall
  rcases hbds with ⟨hbtau, hba, hbcz, hbvc, hbgu, hbdel, hbe, hbdl, hba8, hbell⟩
  let V : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3 :=
    fun k => heightTransportTube (U k) g1 K1
  have hVs (k : Fin 2) : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V k).source :=
    heightTransportTube_closedDisc_source (U k) g1 K1 (hs k)
  have hVh (k : Fin 2) (p : E2 × ℝ) (hp : p ∈ (V k).source) : H (V k p) = p.2 :=
    heightTransportTube_height (U k) g1 K1 u u (hh k) (fun y => (hKH 1 y).1) p hp
  have hVih (k : Fin 2) (y : E3) (hy : y ∈ (V k).target) : ((V k).symm y).2 = H y := by
    have h := hVh k ((V k).symm y) ((V k).map_target hy)
    rw [(V k).right_inv hy] at h
    exact h.symm
  let T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3 := ![V i, V o, Up]
  let cut : Fin 3 → ℝ := ![z, t, v]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  have hTd (k : Fin 3) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T k).source ∧
      ContDiffOn ℝ ∞ (T k) (T k).source ∧
      ContDiffOn ℝ ∞ (T k).symm (T k).target ∧
      (∀ p ∈ (T k).source, H (T k p) = p.2) ∧
      (∀ y ∈ (T k).target, ((T k).symm y).2 = H y) := by
    have hvd (j : Fin 2) :
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V j).source ∧
        ContDiffOn ℝ ∞ (V j) (V j).source ∧
        ContDiffOn ℝ ∞ (V j).symm (V j).target ∧
        (∀ p ∈ (V j).source, H (V j p) = p.2) ∧
        (∀ y ∈ (V j).target, ((V j).symm y).2 = H y) :=
      ⟨hVs j, heightTransportTube_contDiffOn (U j) g1 K1 (hU j),
        heightTransportTube_contDiffOn_symm (U j) g1 K1 (hUi j), hVh j, hVih j⟩
    fin_cases k
    · exact hvd i
    · exact hvd o
    · exact ⟨hUps, hUp, hUpi, hUph, hUpih⟩
  have hslice (k : Fin 2) (X : Set E2) (s : ℝ) :
      K1 '' (U k '' (X ×ˢ ({s} : Set ℝ))) = V k '' (X ×ˢ ({g1 s} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨x, r⟩, ⟨hx, hrmem⟩, rfl⟩, rfl⟩
      have hrs : r = s := mem_singleton_iff.mp hrmem
      subst r
      exact ⟨(x, g1 s), ⟨hx, mem_singleton _⟩,
        heightTransportTube_reparametrized_apply (U k) g1 K1 (x, s)⟩
    · rintro ⟨⟨x, r⟩, ⟨hx, hrmem⟩, rfl⟩
      have hrs : r = g1 s := mem_singleton_iff.mp hrmem
      subst r
      exact ⟨U k (x, s), ⟨(x, s), ⟨hx, mem_singleton _⟩, rfl⟩,
        (heightTransportTube_reparametrized_apply (U k) g1 K1 (x, s)).symm⟩
  refine ⟨b, T, hb, hbtau, hba, hbcz, hbvc, hTd, ?_, ?_, ?_⟩
  · intro s hsb
    have habs : |s - z| ≤ a + 4 * b := abs_le.mpr
      ⟨by dsimp [a]; linarith [hsb.1], by linarith [hsb.2]⟩
    have hse : |s - z| ≤ e := by linarith
    have hsd : |m + (s - z) - m| ≤ delta := by
      rw [add_sub_cancel_left]
      linarith
    have hgs : g1 (m + (s - z)) = s := by
      simpa only [add_sub_cancel] using (haff (s - z) hse).1
    have hlev := congrArg (fun X : Set E3 => K1 '' X) (hlevels _ hsd)
    rw [(hKsets (s - z) hse).1, image_union, hslice, hslice, hgs] at hlev
    have hn := image_mono (hnest _ hsd) (f := K1)
    rw [hslice, hslice, hgs] at hn
    refine ⟨?_, hn⟩
    change S ∩ {y : E3 | H y = s} =
      V i '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
        V o '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
    simpa only [add_sub_cancel] using hlev
  · intro s hsb
    apply hUpcircle
    exact ⟨by linarith [hsb.1], by linarith [hsb.2]⟩
  · intro lambda hlambda hscale
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let cap : Fin 3 → Set E3 := fun k =>
      P.capMap (T k) (cut k) (sign k) 0 (lambda k) '' Qminus
    let Lcyl := T 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)
    let Rband := S ∩ {y : E3 | z ≤ H y ∧ H y ≤ v}
    let M := Rband ∪ Lcyl
    have hcapheight (k : Fin 3) (y : E3) (hy : y ∈ cap k) :
        |H y - cut k| ≤ lambda k * P.heightBound := by
      obtain ⟨q, _, rfl⟩ := hy
      rw [SurgeryCapProfile.capMap_apply, (hTd k).2.2.2.1 _
        ((hTd k).1 ⟨by simpa only [mem_closedBall, dist_zero_right]
          using P.model_fst_norm_le q, mem_univ _⟩)]
      have hsign : |sign k| = 1 := by fin_cases k <;> norm_num [sign]
      simp only [add_sub_cancel_left, zero_add, abs_mul, hsign, one_mul,
        abs_of_pos (hlambda k)]
      exact mul_le_mul_of_nonneg_left (P.height_bound q) (hlambda k).le
    let lam : Fin 2 → ℝ := fun k => if k = i then lambda 0 else lambda 1
    have hlami : lam i = lambda 0 := if_pos rfl
    have hlamo : lam o = lambda 1 := if_neg hio.symm
    have hlam (k : Fin 2) : 0 < lam k := by
      rcases hlabels k with rfl | rfl
      · rw [hlami]; exact hlambda 0
      · rw [hlamo]; exact hlambda 1
    obtain ⟨N, Gs, C, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hGold,
      _, hGoldfix, _, _, _, _, _⟩ := hLower lam hlam
        (by rw [hlami]; linarith [hscale 0]) (by rw [hlamo]; linarith [hscale 1])
        (by rw [hlamo]; linarith [hscale 1])
    let Gold := (Gs i).trans (Gs o)
    let Rold := S ∩ {y : E3 | m ≤ H y}
    let Lold := U o '' (sphere (0 : E2) 1 ×ˢ Icc (m - a) m)
    let south : Fin 2 → Set E3 := fun k =>
      (fun q : UnitTwoSphere => U k ((P.model q).1,
        (if k = i then m else m - a) + lam k * (P.model q).2)) '' Qminus
    change Gold '' S = (Rold ∪ Lold) ∪ south i ∪ south o at hGold
    change ∀ y ∈ Rold ∪ Lold, Gold y = y ∧ Gold.symm y = y at hGoldfix
    have hKzero : g1 m = z := by simpa only [add_zero] using (haff 0 (by simpa using he.le)).1
    have hKlow : g1 (m - a) = t := by
      have ha' : |-a| ≤ e := by rw [abs_neg, abs_of_pos ha]; linarith
      calc
        g1 (m - a) = z + -a := (haff (-a) ha').1
        _ = t := by dsimp [a]; ring
    have hR : K1 '' Rold = S ∩ {y : E3 | z ≤ H y} := by
      simpa only [add_zero] using (hKsets 0 (by simpa using he.le)).2.2.2.2.1
    have hL : K1 '' Lold = Lcyl := by
      ext y
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨(p.1, g1 p.2), ⟨hp.1, ?_⟩,
          heightTransportTube_reparametrized_apply (U o) g1 K1 p⟩
        exact ⟨by rw [← hKlow]; exact (hmono 1).1.monotone hp.2.1,
          by rw [← hKzero]; exact (hmono 1).1.monotone hp.2.2⟩
      · rintro ⟨p, hp, rfl⟩
        refine ⟨U o (p.1, g1.symm p.2), ⟨(p.1, g1.symm p.2), ⟨hp.1, ?_⟩, rfl⟩, rfl⟩
        constructor
        · have h := (hmono 1).2.monotone hp.2.1
          rw [← hKlow, g1.symm_apply_apply] at h
          exact h
        · have h := (hmono 1).2.monotone hp.2.2
          rw [← hKzero, g1.symm_apply_apply] at h
          exact h
    have hcap (k : Fin 2) (j : Fin 3) (hkj : (k = i ∧ j = 0) ∨ (k = o ∧ j = 1)) :
        K1 '' south k = cap j := by
      have hformula (q : UnitTwoSphere) :
          K1 (U k ((P.model q).1,
            (if k = i then m else m - a) + lam k * (P.model q).2)) =
              P.capMap (T j) (cut j) (sign j) 0 (lambda j) q := by
        rcases hkj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hoff : |lambda 0 * (P.model q).2| ≤ e := by
            rw [abs_mul, abs_of_pos (hlambda 0)]
            exact (mul_le_mul_of_nonneg_left (P.height_bound q) (hlambda 0).le).trans
              (by linarith [hscale 0])
          have heq := (haff (lambda 0 * (P.model q).2) hoff).2
          simp only [ite_true, hlami, SurgeryCapProfile.capMap_apply, T, cut, sign,
            Matrix.cons_val_zero, one_mul, zero_add, V, heightTransportTube_apply, m]
          rw [heq]
        · have hbnd : |lambda 1 * (P.model q).2| ≤ lambda 1 * P.heightBound := by
            rw [abs_mul, abs_of_pos (hlambda 1)]
            exact mul_le_mul_of_nonneg_left (P.height_bound q) (hlambda 1).le
          have hoff : |-a + lambda 1 * (P.model q).2| ≤ e := by
            have h := abs_add_le (-a) (lambda 1 * (P.model q).2)
            rw [abs_neg, abs_of_pos ha] at h
            linarith [hscale 1]
          have heq := (haff (-a + lambda 1 * (P.model q).2) hoff).2
          have hsum : z + (-a + lambda 1 * (P.model q).2) =
              t + lambda 1 * (P.model q).2 := by dsimp [a]; ring
          rw [hsum] at heq
          simp only [if_neg hio.symm, hlamo, SurgeryCapProfile.capMap_apply,
            T, cut, sign, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul, zero_add,
            V, heightTransportTube_apply]
          rw [heq]
          congr 3
          dsimp only [m]
          ring
      rw [image_image]
      exact image_congr (fun q _ => hformula q)
    have hci := hcap i 0 (Or.inl ⟨rfl, rfl⟩)
    have hco := hcap o 1 (Or.inr ⟨rfl, rfl⟩)
    let Glow := (K1.symm.trans Gold).trans K1
    have hGlow : Glow '' S = ((S ∩ {y : E3 | z ≤ H y}) ∪ Lcyl) ∪ cap 0 ∪ cap 1 := by
      change (K1 ∘ Gold ∘ K1.symm) '' S = _
      rw [image_comp, image_comp, (hKS 1).2, hGold,
        image_union, image_union, image_union, hR, hL, hci, hco]
    have hGlowfix (y : E3) (hy : y ∈ (S ∩ {y : E3 | z ≤ H y}) ∪ Lcyl) :
        Glow y = y ∧ Glow.symm y = y := by
      have hpre : K1.symm y ∈ Rold ∪ Lold := by
        have hy' : y ∈ K1 '' (Rold ∪ Lold) := by rwa [image_union, hR, hL]
        obtain ⟨x, hx, rfl⟩ := hy'
        simpa only [K1.symm_apply_apply] using hx
      obtain ⟨hf, hi⟩ := hGoldfix (K1.symm y) hpre
      constructor
      · change K1 (Gold (K1.symm y)) = y
        rw [hf, K1.apply_symm_apply]
      · change K1 (Gold.symm (K1.symm y)) = y
        rw [hi, K1.apply_symm_apply]
    obtain ⟨Au, Nu, Gup, Cu, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hGup,
      _, hGupfix, _, _, _, _, _, _, _⟩ :=
      hUpper P (lambda 2) b c (hlambda 2) (by linarith [hscale 2]) (hscale 2)
        (by linarith [hscale 2])
    have hGupcap : Gup '' (S ∩ {y : E3 | v ≤ H y}) = cap 2 := by
      change Gup '' (S ∩ {y : E3 | v ≤ H y}) =
        (fun q : UnitTwoSphere =>
          Up ((P.model q).1, v + -1 * (0 + lambda 2 * (P.model q).2))) '' Qminus
      simpa only [zero_add, neg_one_mul, sub_eq_add_neg] using hGup
    have hUpfixR (y : E3) (hy : y ∈ S ∩ {y : E3 | H y ≤ v}) :
        Gup y = y ∧ Gup.symm y = y := hGupfix y (Or.inl (Or.inr hy))
    have hUpfixLow (y : E3) (hy : H y ≤ c) :
        Gup y = y ∧ Gup.symm y = y := hGupfix y (Or.inr hy)
    have hUpfixL (y : E3) (hy : y ∈ Lcyl) : Gup y = y ∧ Gup.symm y = y := by
      obtain ⟨p, hp, rfl⟩ := hy
      apply hUpfixLow
      rw [(hTd 1).2.2.2.1 _ ((hTd 1).1 ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)]
      exact hp.2.2.trans hzc.le
    have hUpfixCap (k : Fin 3) (hk : k = 0 ∨ k = 1) (y : E3) (hy : y ∈ cap k) :
        Gup y = y ∧ Gup.symm y = y := by
      apply hUpfixLow
      have hh' := (abs_le.mp (hcapheight k y hy)).2
      rcases hk with rfl | rfl
      · change H y - z ≤ lambda 0 * P.heightBound at hh'
        linarith [hscale 0]
      · change H y - t ≤ lambda 1 * P.heightBound at hh'
        linarith [hscale 1]
    have hfixedImage (F : D3) (X : Set E3) (hX : ∀ y ∈ X, F y = y) : F '' X = X := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rwa [hX x hx]
      · intro hy
        exact ⟨y, hy, hX y hy⟩
    have hsplit : S ∩ {y : E3 | z ≤ H y} = Rband ∪ (S ∩ {y : E3 | v ≤ H y}) := by
      ext y
      simp only [Rband, mem_inter_iff, mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨hy, hz'⟩
        rcases le_total (H y) v with hv' | hv'
        · exact Or.inl ⟨hy, hz', hv'⟩
        · exact Or.inr ⟨hy, hv'⟩
      · rintro (⟨hy, hz', _⟩ | ⟨hy, hv'⟩)
        · exact ⟨hy, hz'⟩
        · exact ⟨hy, (hzc.trans hcv).le.trans hv'⟩
    have hbandfix (y : E3) (hy : y ∈ Rband) : Gup y = y ∧ Gup.symm y = y :=
      hUpfixR y ⟨hy.1, hy.2.2⟩
    have hUnion : (⋃ k : Fin 3, cap k) = cap 0 ∪ cap 1 ∪ cap 2 := by
      ext y
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨k, hk⟩
        fin_cases k
        · exact Or.inl (Or.inl hk)
        · exact Or.inl (Or.inr hk)
        · exact Or.inr hk
      · rintro ((h | h) | h)
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
    let G := Glow.trans Gup
    have hG : G '' S = M ∪ ⋃ k : Fin 3, cap k := by
      change (Gup ∘ Glow) '' S = _
      rw [image_comp, hGlow, hsplit, image_union, image_union, image_union,
        image_union, hfixedImage Gup Rband (fun y hy => (hbandfix y hy).1), hGupcap,
        hfixedImage Gup Lcyl (fun y hy => (hUpfixL y hy).1),
        hfixedImage Gup (cap 0) (fun y hy => (hUpfixCap 0 (Or.inl rfl) y hy).1),
        hfixedImage Gup (cap 1) (fun y hy => (hUpfixCap 1 (Or.inr rfl) y hy).1), hUnion]
      dsimp only [M]
      ext y
      simp only [mem_union]
      tauto
    refine ⟨G, hG, ?_, ?_, hcapheight⟩
    · rw [← hG]
      exact G.symm_image_image S
    · intro y hy
      have hlow : y ∈ (S ∩ {y : E3 | z ≤ H y}) ∪ Lcyl :=
        hy.elim (fun hy => Or.inl ⟨hy.1, hy.2.1⟩) Or.inr
      obtain ⟨hf, hi⟩ := hGlowfix y hlow
      have hup := hy.elim (hbandfix y) (hUpfixL y)
      constructor
      · change Gup (Glow y) = y
        rw [hf, hup.1]
      · change Glow.symm (Gup.symm y) = y
        rw [hup.2, hi]

end PoincareConjecture.M25.Topology3D
