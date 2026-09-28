import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RelativeHeightField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MorseRadialChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HorizontalMembership
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LocalizedClockGraph











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 3000000 in





theorem exists_relative_collar_band_verticalization
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (c sigma theta R b : ℝ)
    (_hsigma : sigma * sigma = 1) (_htheta : theta = -sigma)
    (hR : 0 < R) (hb : 0 < b)
    (P : OpenPartialHomeomorph (ℝ × ℝ) E2)
    (_hP : ContDiffOn ℝ ∞ P P.source) (_hPi : ContDiffOn ℝ ∞ P.symm P.target)
    (A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3)
    (hA : ContDiffOn ℝ ∞ A A.source) (hAi : ContDiffOn ℝ ∞ A.symm A.target)
    (hPsource : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ R ^ 2} ⊆ P.source)
    (hAsource : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ R ^ 2} ×ˢ
      Icc (c - 4 * b) (c + 4 * b) ⊆ A.source)
    (hAP : ∀ s ∈ {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ R ^ 2},
      ∀ z : ℝ, |z - c| ≤ 4 * b →
        A (s, z) = (heightPlaneCoordinates u).symm (P s, z))
    (hAheight : ∀ w ∈ A.source, ⟪(u : E3), A w⟫_ℝ = w.2)
    (hAgraph : ∀ w ∈ A.source,
      A w ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        w.2 = c + (sigma * w.1.1 ^ 2 + theta * w.1.2 ^ 2))
    (hreg : ∀ q ∈ {q : UnitTwoSphere |
        |⟪(u : E3), psi (q, 0)⟫_ℝ - c| ≤ 2 * b ∧
        horizontalBandProjection u (psi (q, 0)) ∉
          P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (R / 4) ^ 2}},
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let S : Set E3 := range j
    let Q : ℝ × ℝ → ℝ := fun s => sigma * s.1 ^ 2 + theta * s.2 ^ 2
    let B : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Do : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    let r : ℕ → ℝ := fun i => (((i : ℝ) + 1) / 8) * R
    let V : ℕ → Set E2 := fun i => P '' Do (r i)
    let Kunit : Set UnitTwoSphere := {q | |H (j q) - c| ≤ 2 * b ∧ pi (j q) ∉ V 1}
    let Cprot : Set E3 := {y | pi y ∈ closure (V 0)} ∪ {y | 3 * b ≤ |H y - c|}
    let Ssafe : Set E3 := {y | y ∈ S ∧ |H y - c| ≤ b ∧ pi y ∉ V 2}
    let Omega : Set E3 := {y | |H y - c| < 2 * b ∧ pi y ∉ closure (V 1)}
    ∃ (F : E3 → E3) (hF : ContDiff ℝ ∞ F) (hsF : HasCompactSupport F)
      (KF LF : ℝ≥0) (hKF : LipschitzWith KF F) (hLF : ∀ y, ‖F y‖ ≤ LF)
      (KV LV : ℝ≥0)
      (hKV : LipschitzWith KV (clockField (horizontalBandField u F)))
      (hLV : ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ LV)
      (tau delta epsilon : ℝ) (chi : ℝ → ℝ)
      (hchi : ContDiff ℝ ∞ chi) (hschi : HasCompactSupport chi)
      (I : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (Anew : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3),
      let Vf := horizontalBandField u F
      let Phi := boundedFlow F hKF hLF
      let Xi := clockEvolution Vf hKV hLV
      let Gamma : Set E2 := {x | L.symm (x, c) ∈ S}
      let Snew : Set E3 := (I 1) '' S
      let a : ℝ → ℝ → ℝ := fun s z => c + s * chi z * (z - c)
      let Ciso : Set E3 := L.symm '' ((Prod.snd '' tsupport Vf) ×ˢ tsupport chi)
      let U6 : Set ((ℝ × ℝ) × ℝ) := Do (r 6) ×ˢ Ioo (c - 4 * b) (c + 4 * b)
      let hU6 : IsOpen U6 :=
        (morseRadialDisc_geometry (r 6) (by dsimp [r]; positivity)).1.prod isOpen_Ioo
      let A6 := Anew.restrOpen U6 hU6
      let O : Set (E2 × ℝ) := (V 5 \ closure (V 4)) ×ˢ Ioo (c - epsilon) (c + epsilon)
      tsupport F ⊆ (psi '' (univ ×ˢ Ioo (-1) 1)) \ Cprot ∧
      (∀ q ∈ Kunit, H (F (j q)) = 1) ∧
      (∀ y ∈ S, ∀ t : ℝ, Phi y t ∈ S) ∧
      (∀ y ∈ Cprot, ∀ t : ℝ, Phi y t = y) ∧
      0 < tau ∧ tau ≤ b / 4 ∧
      (∀ y ∈ Ssafe, ∀ t : ℝ, |t| ≤ tau → Phi y t ∈ Omega ∧ H (Phi y t) = H y + t) ∧
      0 < delta ∧ Metric.thickening delta (closure (V 2)) ⊆ V 3 ∧
      Metric.thickening delta (closure (V 3)) ⊆ V 4 ∧
      Metric.thickening delta (closure (V 5)) ⊆ V 6 ∧
      0 < epsilon ∧ epsilon ≤ b / 8 ∧ epsilon ≤ tau / 4 ∧
      epsilon ≤ delta / (8 * ((LV : ℝ) + 1)) ∧ epsilon ≤ (r 0) ^ 2 / 8 ∧
      2 * (LV : ℝ) * epsilon < delta ∧
      (∀ z, chi z ∈ Icc 0 1) ∧
      (∀ z, |z - c| ≤ epsilon → chi z = 1) ∧
      tsupport chi ⊆ Ioo (c - 2 * epsilon) (c + 2 * epsilon) ∧
      (∀ s : ℝ, ∀ y : E3,
        I s y = L.symm (Xi (a s (H y)) c (pi y), H y) ∧
        (I s).symm y = L.symm (Xi c (a s (H y)) (pi y), H y)) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => I p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (I p.1).symm p.2) ∧
      (∀ y, I 0 y = y) ∧
      (∀ s y, H (I s y) = H y ∧ H ((I s).symm y) = H y) ∧
      IsCompact Ciso ∧
      (∀ s : ℝ, tsupport (fun y => I s y - y) ⊆ Ciso ∧
        tsupport (fun y => (I s).symm y - y) ⊆ Ciso) ∧
      (∀ s y, (pi y ∈ closure (V 0) ∨ H y = c ∨ 2 * epsilon ≤ |H y - c|) →
        I s y = y ∧ (I s).symm y = y) ∧
      (∀ x : E2, x ∉ V 3 → ∀ z : ℝ, |z - c| ≤ epsilon →
        (L.symm (Xi c z x, z) ∈ S ↔ x ∈ Gamma)) ∧
      (∀ x : E2, x ∉ V 3 → ∀ z : ℝ, |z - c| ≤ epsilon →
        (L.symm (x, z) ∈ Snew ↔ x ∈ Gamma)) ∧
      (∀ y ∈ S, |H y - c| ≤ epsilon → pi y ∉ V 4 →
        let x := Xi (H y) c (pi y)
        x ∉ V 3 ∧ x ∈ Gamma ∧ I 1 y = L.symm (x, H y) ∧
        y = L.symm (Xi c (H y) x, H y)) ∧
      Anew = A.trans ((I 1).toHomeomorph.toOpenPartialHomeomorph) ∧
      Anew.source = A.source ∧ Anew.target = (I 1) '' A.target ∧
      ContDiffOn ℝ ∞ Anew Anew.source ∧ ContDiffOn ℝ ∞ Anew.symm Anew.target ∧
      (∀ w ∈ Anew.source, H (Anew w) = w.2 ∧ (Anew w ∈ Snew ↔ w.2 = c + Q w.1)) ∧
      (∀ s ∈ B R, ∀ z : ℝ, |z - c| ≤ epsilon →
        Anew (s, z) = L.symm (Xi z c (P s), z)) ∧
      (∀ s ∈ B (r 0), ∀ z : ℝ, |z - c| ≤ 4 * b → Anew (s, z) = A (s, z)) ∧
      IsOpen O ∧ A6.source = U6 ∧ A6.target = Anew '' U6 ∧
      ContDiffOn ℝ ∞ A6 A6.source ∧ ContDiffOn ℝ ∞ A6.symm A6.target ∧
      L.symm '' O ⊆ A6.target ∧
      (∀ p ∈ O, (P.symm (Xi c p.2 p.1), p.2) ∈ U6 ∧
        Anew.symm (L.symm p) = (P.symm (Xi c p.2 p.1), p.2)) ∧
      Gamma ∩ (V 5 \ closure (V 4)) =
        P '' {s | s ∈ Do (r 5) ∧ s ∉ B (r 4) ∧ Q s = 0} ∧
      Snew ∩ (L.symm '' O) = L.symm ''
        ((Gamma ∩ (V 5 \ closure (V 4))) ×ˢ Ioo (c - epsilon) (c + epsilon)) := by
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let S := range j
  let Q : ℝ × ℝ → ℝ := fun s => sigma * s.1 ^ 2 + theta * s.2 ^ 2
  let B : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
  let Do : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
  let r : ℕ → ℝ := fun i => (((i : ℝ) + 1) / 8) * R
  let V : ℕ → Set E2 := fun i => P '' Do (r i)
  let Kunit : Set UnitTwoSphere := {q | |H (j q) - c| ≤ 2 * b ∧ pi (j q) ∉ V 1}
  let Cprot : Set E3 := {y | pi y ∈ closure (V 0)} ∪ {y | 3 * b ≤ |H y - c|}
  let Ssafe : Set E3 := {y | y ∈ S ∧ |H y - c| ≤ b ∧ pi y ∉ V 2}
  let Omega : Set E3 := {y | |H y - c| < 2 * b ∧ pi y ∉ closure (V 1)}
  have hrpos (i : ℕ) : 0 < r i := by dsimp [r]; positivity
  have hrle (i : ℕ) (hi : i ≤ 6) : r i ≤ R := by
    have hi' : (i : ℝ) ≤ 6 := by exact_mod_cast hi
    dsimp [r]
    nlinarith
  have hrlt (i k : ℕ) (hik : i < k) : r i < r k := by
    have hik' : (i : ℝ) < k := by exact_mod_cast hik
    dsimp [r]
    exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (by linarith) (by norm_num)) hR
  obtain ⟨hgeom, hnest0⟩ := morseRadialChart_geometry P R hR hPsource
  have hgeom' (i : ℕ) (hi : i ≤ 6) : IsOpen (V i) ∧ IsCompact (closure (V i)) ∧
      closure (V i) = P '' B (r i) := hgeom (r i) (hrpos i) (hrle i hi)
  have hnest (i k : ℕ) (hik : i < k) (hk : k ≤ 6) : closure (V i) ⊆ V k :=
    hnest0 (r i) (r k) (hrpos i) (hrlt i k hik) (hrle k hk)
  have hmono (i k : ℕ) (hik : i < k) (hk : k ≤ 6) : V i ⊆ V k :=
    subset_closure.trans (hnest i k hik hk)
  have hBR (i : ℕ) (hi : i ≤ 6) : B (r i) ⊆ B R := by
    intro s hs
    exact hs.trans ((sq_le_sq₀ (hrpos i).le hR.le).mpr (hrle i hi))
  have hDoB (a : ℝ) : Do a ⊆ B a := by
    intro s hs
    change s.1 ^ 2 + s.2 ^ 2 < a ^ 2 at hs
    exact hs.le
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  have hScompact : IsCompact S := isCompact_range hj
  have hK : IsCompact Kunit :=
    ((isClosed_le ((H.continuous.comp hj).sub continuous_const).abs continuous_const).inter
      ((hgeom' 1 (by omega)).1.isClosed_compl.preimage (pi.continuous.comp hj))).isCompact
  have hC : IsClosed Cprot :=
    (isClosed_closure.preimage pi.continuous).union
      (isClosed_le continuous_const (H.continuous.sub continuous_const).abs)
  have hKC : Disjoint (j '' Kunit) Cprot := by
    apply Set.disjoint_left.mpr
    rintro y ⟨q, hq, rfl⟩ hy
    rcases hy with hp | hh
    · exact hq.2 (hnest 0 1 (by omega) (by omega) hp)
    · have hq' : |H (j q) - c| ≤ 2 * b := hq.1
      change 3 * b ≤ |H (j q) - c| at hh
      linarith
  have hreg' : ∀ q ∈ Kunit, mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0 := by
    intro q hq
    apply hreg q
    refine ⟨hq.1, ?_⟩
    have hr1 : r 1 = R / 4 := by dsimp [r]; ring
    have hn := hq.2
    change pi (j q) ∉ P '' Do (r 1) at hn
    rwa [hr1] at hn
  obtain ⟨F, hF, hsF, hFs, hunit, hflows⟩ :=
    exists_relative_collar_height_field psi hpsi (u : E3) hK hreg' hC hKC
  obtain ⟨KF, LF, hKF, hLF⟩ := compactField_bounds F hF hsF
  obtain ⟨hSflow0, hCflow⟩ := hflows KF LF hKF hLF
  let Phi := boundedFlow F hKF hLF
  have hSflow : ∀ y ∈ S, ∀ t : ℝ, Phi y t ∈ S := by
    rintro y ⟨q, rfl⟩ t
    exact hSflow0 q t
  obtain ⟨KV, LV, hKV, hLV⟩ := horizontalBandField_clock_bounds u F hF hsF
  let Vf := horizontalBandField u F
  let Xi := clockEvolution Vf hKV hLV
  have hVf := horizontalBandField_contDiff u F hF
  have hsVf := horizontalBandField_hasCompactSupport u F hsF
  have hSafe : IsCompact Ssafe := hScompact.inter_right
    ((isClosed_le (H.continuous.sub continuous_const).abs continuous_const).inter
      ((hgeom' 2 (by omega)).1.isClosed_compl.preimage pi.continuous))
  have hOmega : IsOpen Omega :=
    (isOpen_lt (H.continuous.sub continuous_const).abs continuous_const).inter
      (isClosed_closure.isOpen_compl.preimage pi.continuous)
  have hSafeOmega : Ssafe ⊆ S ∩ Omega := by
    rintro y ⟨hy, hh, hp⟩
    exact ⟨hy, by linarith, fun hc => hp (hnest 1 2 (by omega) (by omega) hc)⟩
  have hunitOmega : ∀ y ∈ S ∩ Omega, H (F y) = 1 := by
    rintro y ⟨⟨q, rfl⟩, hh, hp⟩
    exact hunit q ⟨hh.le, fun hc => hp (subset_closure hc)⟩
  obtain ⟨tau0, htau0, htracks0⟩ := exists_boundedFlow_unit_height_interval F hKF hLF H
    hSafe hOmega hSafeOmega hSflow hunitOmega
  let tau := min tau0 (b / 4)
  have htau : 0 < tau := lt_min htau0 (by positivity)
  have htaub : tau ≤ b / 4 := min_le_right _ _
  have htracks (y : E3) (hy : y ∈ Ssafe) (t : ℝ) (ht : |t| ≤ tau) :
      Phi y t ∈ Omega ∧ H (Phi y t) = H y + t :=
    htracks0 y hy t (ht.trans (min_le_left _ _))
  obtain ⟨d23, hd23, hg23⟩ := (hgeom' 2 (by omega)).2.1.exists_thickening_subset_open
    (hgeom' 3 (by omega)).1 (hnest 2 3 (by omega) (by omega))
  obtain ⟨d34, hd34, hg34⟩ := (hgeom' 3 (by omega)).2.1.exists_thickening_subset_open
    (hgeom' 4 (by omega)).1 (hnest 3 4 (by omega) (by omega))
  obtain ⟨d56, hd56, hg56⟩ := (hgeom' 5 (by omega)).2.1.exists_thickening_subset_open
    (hgeom' 6 (by omega)).1 (hnest 5 6 (by omega) (by omega))
  let delta := min d23 (min d34 d56)
  have hdelta : 0 < delta := lt_min hd23 (lt_min hd34 hd56)
  have hgap23 : Metric.thickening delta (closure (V 2)) ⊆ V 3 :=
    (Metric.thickening_mono (min_le_left _ _) _).trans hg23
  have hgap34 : Metric.thickening delta (closure (V 3)) ⊆ V 4 :=
    (Metric.thickening_mono ((min_le_right _ _).trans (min_le_left _ _)) _).trans hg34
  have hgap56 : Metric.thickening delta (closure (V 5)) ⊆ V 6 :=
    (Metric.thickening_mono ((min_le_right _ _).trans (min_le_right _ _)) _).trans hg56
  let epsilon := min (b / 8) (min (tau / 4)
    (min (delta / (8 * ((LV : ℝ) + 1))) ((r 0) ^ 2 / 8)))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (div_pos (sq_pos_of_pos (hrpos 0)) (by norm_num))))
  have heb : epsilon ≤ b / 8 := min_le_left _ _
  have het : epsilon ≤ tau / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hed : epsilon ≤ delta / (8 * ((LV : ℝ) + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have her : epsilon ≤ (r 0) ^ 2 / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmove2 : 2 * (LV : ℝ) * epsilon < delta := by
    have hm := (le_div_iff₀ (by positivity : 0 < 8 * ((LV : ℝ) + 1))).mp hed
    nlinarith [LV.coe_nonneg, mul_nonneg LV.coe_nonneg hepsilon.le]
  have hmove : (LV : ℝ) * epsilon < delta := by
    nlinarith [mul_nonneg LV.coe_nonneg hepsilon.le]
  have hetau : epsilon < tau := by linarith
  have heb' : epsilon ≤ b := by linarith
  obtain ⟨chi, hchi, hschi, hchis, hchinear, hchirange⟩ :=
    exists_compact_smooth_cutoff (isCompact_Icc : IsCompact (Icc (c - epsilon) (c + epsilon)))
      (isOpen_Ioo : IsOpen (Ioo (c - 2 * epsilon) (c + 2 * epsilon)))
      (by intro z hz; constructor <;> linarith [hz.1, hz.2])
  have hchione (z : ℝ) (hz : |z - c| ≤ epsilon) : chi z = 1 := by
    apply subset_of_mem_nhdsSet hchinear
    obtain ⟨hl, hh⟩ := abs_le.mp hz
    exact ⟨by linarith, by linarith⟩
  let a : ℝ → ℝ → ℝ := fun s z => c + s * chi z * (z - c)
  let G := localizedClockGraphDiffeomorph Vf hKV hLV hVf hsVf chi hchi c
  let I (s : ℝ) := L.toDiffeomorph.trans ((G s).symm.trans L.toDiffeomorph.symm)
  let Gamma : Set E2 := {x | L.symm (x, c) ∈ S}
  let Snew : Set E3 := (I 1) '' S
  let Ciso : Set E3 := L.symm '' ((Prod.snd '' tsupport Vf) ×ˢ tsupport chi)
  have hcoord (y : E3) : L y = (pi y, H y) :=
    Prod.ext rfl (heightPlaneCoordinates_snd u y)
  have hrec (y : E3) : L.symm (pi y, H y) = y := by
    rw [← hcoord, L.symm_apply_apply]
  have hHlift (x : E2) (z : ℝ) : H (L.symm (x, z)) = z :=
    horizontalBandLift_height u z x
  have hplift (x : E2) (z : ℝ) : pi (L.symm (x, z)) = x :=
    horizontalBandProjection_lift u z x
  have hI (s : ℝ) (y : E3) :
      I s y = L.symm (Xi (a s (H y)) c (pi y), H y) ∧
      (I s).symm y = L.symm (Xi c (a s (H y)) (pi y), H y) := by
    change L.symm ((G s).symm (L y)) = _ ∧ L.symm (G s (L y)) = _
    rw [hcoord]
    exact ⟨rfl, rfl⟩
  have ha : ContDiff ℝ ∞ (fun p : ℝ × E3 => a p.1 (H p.2)) :=
    contDiff_const.add ((contDiff_fst.mul (hchi.comp (H.contDiff.comp contDiff_snd))).mul
      ((H.contDiff.comp contDiff_snd).sub contDiff_const))
  have hXismooth := clockEvolution_contDiff Vf hKV hLV hVf hsVf
  have hIsmooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => I p.1 p.2) := by
    have hf : ContDiff ℝ ∞ (fun p : ℝ × E3 =>
        L.symm (Xi (a p.1 (H p.2)) c (pi p.2), H p.2)) :=
      L.symm.contDiff.comp ((hXismooth.comp
        ((ha.prodMk contDiff_const).prodMk (pi.contDiff.comp contDiff_snd))).prodMk
          (H.contDiff.comp contDiff_snd))
    have heq : (fun p : ℝ × E3 => I p.1 p.2) =
        (fun p => L.symm (Xi (a p.1 (H p.2)) c (pi p.2), H p.2)) :=
      funext (fun p => (hI p.1 p.2).1)
    rw [heq]
    exact hf
  have hIinverse : ContDiff ℝ ∞ (fun p : ℝ × E3 => (I p.1).symm p.2) := by
    have hf : ContDiff ℝ ∞ (fun p : ℝ × E3 =>
        L.symm (Xi c (a p.1 (H p.2)) (pi p.2), H p.2)) :=
      L.symm.contDiff.comp ((hXismooth.comp
        ((contDiff_const.prodMk ha).prodMk (pi.contDiff.comp contDiff_snd))).prodMk
          (H.contDiff.comp contDiff_snd))
    have heq : (fun p : ℝ × E3 => (I p.1).symm p.2) =
        (fun p => L.symm (Xi c (a p.1 (H p.2)) (pi p.2), H p.2)) :=
      funext (fun p => (hI p.1 p.2).2)
    rw [heq]
    exact hf
  have hIzero (y : E3) : I 0 y = y := by
    rw [(hI 0 y).1]
    simpa only [a, zero_mul, add_zero, Xi, clockEvolution_self] using hrec y
  have hIheight (s : ℝ) (y : E3) :
      H (I s y) = H y ∧ H ((I s).symm y) = H y := by
    rw [(hI s y).1, (hI s y).2, hHlift, hHlift]
    exact ⟨rfl, rfl⟩
  have hCiso : IsCompact Ciso :=
    ((hsVf.isCompact.image continuous_snd).prod hschi.isCompact).image L.symm.continuous
  have htransport (g : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
      (E2 × ℝ) (E2 × ℝ) ∞)
      (hg : tsupport (fun p => g p - p) ⊆ (Prod.snd '' tsupport Vf) ×ˢ tsupport chi) :
      tsupport (fun y => L.symm (g (L y)) - y) ⊆ Ciso := by
    apply closure_minimal ?_ hCiso.isClosed
    intro y hy
    have hne : g (L y) ≠ L y := by
      intro heq
      apply hy
      change L.symm (g (L y)) - y = 0
      rw [heq, L.symm_apply_apply, sub_self]
    exact ⟨L y, hg (subset_tsupport _ (sub_ne_zero.mpr hne)), L.symm_apply_apply y⟩
  have hIsupport (s : ℝ) : tsupport (fun y => I s y - y) ⊆ Ciso ∧
      tsupport (fun y => (I s).symm y - y) ⊆ Ciso := by
    have hg := localizedClockGraphDiffeomorph_tsupport_subset Vf hKV hLV hVf hsVf chi hchi c s
    exact ⟨htransport (G s).symm hg.2, htransport (G s) hg.1⟩
  have hVzero (z : ℝ) (x : E2) (hx : x ∈ closure (V 0)) : Vf (z, x) = 0 := by
    have hz : F (L.symm (x, z)) = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hf
      apply (hFs hf).2
      apply Or.inl
      change pi (L.symm (x, z)) ∈ closure (V 0)
      rwa [hplift])
    change pi (F (L.symm (x, z))) = 0
    rw [hz, map_zero]
  have hIfix (s : ℝ) (y : E3)
      (hy : pi y ∈ closure (V 0) ∨ H y = c ∨ 2 * epsilon ≤ |H y - c|) :
      I s y = y ∧ (I s).symm y = y := by
    rcases hy with hp | hh | hz
    · have hg := localizedClockGraphDiffeomorph_fixed_cylinder Vf hKV hLV hVf hsVf
        chi hchi c hVzero s (H y) (pi y) hp
      change L.symm ((G s).symm (L y)) = y ∧ L.symm (G s (L y)) = y
      rw [hcoord, hg.1, hg.2, hrec]
      exact ⟨rfl, rfl⟩
    · have ha : a s (H y) = c := by simp only [a, hh, sub_self, mul_zero, add_zero]
      rw [(hI s y).1, (hI s y).2, ha]
      simpa only [Xi, clockEvolution_self] using And.intro (hrec y) (hrec y)
    · have hchi0 : chi (H y) = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hm
        have hm' := hchis hm
        have hlt : |H y - c| < 2 * epsilon := abs_lt.mpr
          ⟨by linarith [hm'.1], by linarith [hm'.2]⟩
        exact (not_lt_of_ge hz) hlt)
      have ha : a s (H y) = c := by simp only [a, hchi0, mul_zero, zero_mul, add_zero]
      rw [(hI s y).1, (hI s y).2, ha]
      simpa only [Xi, clockEvolution_self] using And.intro (hrec y) (hrec y)
  have hclockmem (x : E2) (hx : x ∉ V 3) (z : ℝ) (hz : |z - c| ≤ epsilon) :
      L.symm (Xi c z x, z) ∈ S ↔ x ∈ Gamma :=
    horizontalBand_clockEvolution_mem_iff_of_margin u F hKF hLF hKV hLV
      (S := S) (A := Ssafe) (N := V 2) (W := V 3)
      (τ := tau) (c := c) (b := b) (ε := epsilon) (δ := delta)
      hepsilon hetau heb' hdelta
      ((Metric.thickening_subset_of_subset delta subset_closure).trans hgap23) hmove
      hSflow (fun y hy t ht => (htracks y hy t ht).2)
      (fun y hy hh hp => ⟨hy, hh, hp⟩) x hx z hz
  have haone (z : ℝ) (hz : |z - c| ≤ epsilon) : a 1 z = z := by
    dsimp [a]
    rw [hchione z hz]
    ring
  have hnewmem0 (y : E3) : y ∈ Snew ↔ (I 1).symm y ∈ S := by
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa only [Diffeomorph.symm_apply_apply] using hv
    · intro hy
      exact ⟨(I 1).symm y, hy, (I 1).apply_symm_apply y⟩
  have hnewmem (x : E2) (hx : x ∉ V 3) (z : ℝ) (hz : |z - c| ≤ epsilon) :
      L.symm (x, z) ∈ Snew ↔ x ∈ Gamma := by
    rw [hnewmem0, (hI 1 _).2, hHlift, hplift, haone z hz]
    exact hclockmem x hx z hz
  have hdist (s t : ℝ) (x : E2) (hst : |t - s| ≤ epsilon) :
      dist (Xi s t x) x < delta := by
    rw [dist_eq_norm]
    exact (clockEvolution_norm_sub_le Vf hKV hLV s t x).trans_lt
      ((mul_le_mul_of_nonneg_left hst LV.coe_nonneg).trans_lt hmove)
  have hreverse (y : E3) (hy : y ∈ S) (hh : |H y - c| ≤ epsilon) (hp : pi y ∉ V 4) :
      let x := Xi (H y) c (pi y)
      x ∉ V 3 ∧ x ∈ Gamma ∧ I 1 y = L.symm (x, H y) ∧
        y = L.symm (Xi c (H y) x, H y) := by
    let x := Xi (H y) c (pi y)
    have hxdist : dist x (pi y) < delta := hdist (H y) c (pi y) (by rwa [abs_sub_comm])
    have hx : x ∉ V 3 := by
      intro hm
      exact hp (hgap34 (Metric.mem_thickening_iff.mpr
        ⟨x, subset_closure hm, by rwa [dist_comm]⟩))
    have hback : y = L.symm (Xi c (H y) x, H y) := by
      dsimp [x, Xi]
      rw [clockEvolution_reverse, hrec]
    refine ⟨hx, (hclockmem x hx (H y) hh).mp (hback ▸ hy), ?_, hback⟩
    rw [(hI 1 y).1, haone (H y) hh]
  let Anew := A.trans ((I 1).toHomeomorph.toOpenPartialHomeomorph)
  have hAnewsource : Anew.source = A.source := by
    ext w
    exact and_iff_left (mem_univ _)
  have hAnewtarget : Anew.target = (I 1) '' A.target := by
    ext y
    change (y ∈ univ ∧ (I 1).symm y ∈ A.target) ↔ y ∈ (I 1) '' A.target
    constructor
    · intro hy
      exact ⟨(I 1).symm y, hy.2, (I 1).apply_symm_apply y⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨mem_univ _, by simpa only [Diffeomorph.symm_apply_apply] using hw⟩
  have hAnewsmooth : ContDiffOn ℝ ∞ Anew Anew.source := by
    rw [hAnewsource]
    change ContDiffOn ℝ ∞ (fun w => I 1 (A w)) A.source
    simpa only [Function.comp_def] using
      hIsmooth.comp_contDiffOn (contDiff_const.contDiffOn.prodMk hA)
  have hI1i : ContDiff ℝ ∞ (I 1).symm := by
    rw [← contDiffOn_univ]
    simpa only [Function.comp_def, id_eq] using
      hIinverse.comp_contDiffOn (contDiff_const.contDiffOn.prodMk contDiff_id.contDiffOn)
  have hAnewinverse : ContDiffOn ℝ ∞ Anew.symm Anew.target :=
    by
      rw [hAnewtarget]
      change ContDiffOn ℝ ∞ (fun y => A.symm ((I 1).symm y)) ((I 1) '' A.target)
      exact hAi.comp hI1i.contDiffOn (by
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        simpa only [Diffeomorph.symm_apply_apply] using hy)
  have hAnewgraph (w : (ℝ × ℝ) × ℝ) (hw : w ∈ Anew.source) :
      H (Anew w) = w.2 ∧ (Anew w ∈ Snew ↔ w.2 = c + Q w.1) := by
    have hwA : w ∈ A.source := hAnewsource ▸ hw
    refine ⟨(hIheight 1 (A w)).1.trans (hAheight w hwA), ?_⟩
    change I 1 (A w) ∈ Snew ↔ _
    rw [hnewmem0, Diffeomorph.symm_apply_apply]
    exact hAgraph w hwA
  have hAnewbuffer (s : ℝ × ℝ) (hs : s ∈ B R) (z : ℝ) (hz : |z - c| ≤ epsilon) :
      Anew (s, z) = L.symm (Xi z c (P s), z) := by
    change I 1 (A (s, z)) = _
    rw [hAP s hs z (by linarith), (hI 1 _).1, hHlift, hplift, haone z hz]
  have hAnewfixed (s : ℝ × ℝ) (hs : s ∈ B (r 0)) (z : ℝ)
      (hz : |z - c| ≤ 4 * b) : Anew (s, z) = A (s, z) := by
    apply (hIfix 1 (A (s, z)) _).1
    apply Or.inl
    rw [hAP s (hBR 0 (by omega) hs) z hz, hplift, (hgeom' 0 (by omega)).2.2]
    exact ⟨s, hs, rfl⟩
  let U6 : Set ((ℝ × ℝ) × ℝ) := Do (r 6) ×ˢ Ioo (c - 4 * b) (c + 4 * b)
  have hU6 : IsOpen U6 := (morseRadialDisc_geometry (r 6) (hrpos 6)).1.prod isOpen_Ioo
  have hU6A : U6 ⊆ Anew.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    rw [hAnewsource]
    exact hAsource ⟨hBR 6 (by omega) (hDoB (r 6) hs), hz.1.le, hz.2.le⟩
  let A6 := Anew.restrOpen U6 hU6
  have hA6source : A6.source = U6 := inter_eq_right.mpr hU6A
  have hA6target : A6.target = Anew '' U6 := by
    rw [← A6.image_source_eq_target, hA6source]
    rfl
  have hA6smooth : ContDiffOn ℝ ∞ A6 A6.source := hAnewsmooth.mono inter_subset_left
  have hA6inverse : ContDiffOn ℝ ∞ A6.symm A6.target := hAnewinverse.mono inter_subset_left
  let O : Set (E2 × ℝ) := (V 5 \ closure (V 4)) ×ˢ Ioo (c - epsilon) (c + epsilon)
  have hO : IsOpen O := ((hgeom' 5 (by omega)).1.sdiff isClosed_closure).prod isOpen_Ioo
  have hOheight (p : E2 × ℝ) (hp : p ∈ O) : |p.2 - c| ≤ epsilon :=
    (abs_lt.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩).le
  have hOchart (p : E2 × ℝ) (hp : p ∈ O) :
      (P.symm (Xi c p.2 p.1), p.2) ∈ U6 ∧
        Anew (P.symm (Xi c p.2 p.1), p.2) = L.symm p := by
    have hv : Xi c p.2 p.1 ∈ V 6 := hgap56 (Metric.mem_thickening_iff.mpr
      ⟨p.1, subset_closure hp.1.1, hdist c p.2 p.1 (hOheight p hp)⟩)
    obtain ⟨s, hs, heq⟩ := hv
    have hsP := hPsource (hBR 6 (by omega) (hDoB (r 6) hs))
    have hinv : P.symm (Xi c p.2 p.1) = s := by rw [← heq, P.left_inv hsP]
    refine ⟨⟨hinv ▸ hs, by constructor <;> linarith [hp.2.1, hp.2.2]⟩, ?_⟩
    rw [hinv, hAnewbuffer s (hBR 6 (by omega) (hDoB (r 6) hs)) p.2 (hOheight p hp), heq]
    simp only [Xi, clockEvolution_reverse, Prod.eta]
  have hOtarget : L.symm '' O ⊆ A6.target := by
    rintro y ⟨p, hp, rfl⟩
    rw [hA6target]
    exact ⟨(P.symm (Xi c p.2 p.1), p.2), (hOchart p hp).1, (hOchart p hp).2⟩
  have hOinverse (p : E2 × ℝ) (hp : p ∈ O) :
      (P.symm (Xi c p.2 p.1), p.2) ∈ U6 ∧
        Anew.symm (L.symm p) = (P.symm (Xi c p.2 p.1), p.2) := by
    refine ⟨(hOchart p hp).1, ?_⟩
    rw [← (hOchart p hp).2]
    exact Anew.left_inv (hU6A (hOchart p hp).1)
  have hAc (s : ℝ × ℝ) (hs : s ∈ B R) :
      (s, c) ∈ A.source ∧ A (s, c) = L.symm (P s, c) :=
    ⟨hAsource ⟨hs, by constructor <;> linarith⟩,
      hAP s hs c (by simp only [sub_self, abs_zero]; positivity)⟩
  have hannulus : Gamma ∩ (V 5 \ closure (V 4)) =
      P '' {s | s ∈ Do (r 5) ∧ s ∉ B (r 4) ∧ Q s = 0} := by
    ext x
    constructor
    · rintro ⟨hxG, hxV, hxB⟩
      obtain ⟨s, hs, rfl⟩ := hxV
      have hsR := hBR 5 (by omega) (hDoB (r 5) hs)
      have hsnot : s ∉ B (r 4) := by
        intro hm
        exact hxB ((hgeom' 4 (by omega)).2.2.symm ▸ ⟨s, hm, rfl⟩)
      have hg : c = c + Q s := (hAgraph (s, c) (hAc s hsR).1).mp
        ((hAc s hsR).2.symm ▸ hxG)
      exact ⟨s, ⟨hs, hsnot, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hsnot, hQ⟩, rfl⟩
      have hsR := hBR 5 (by omega) (hDoB (r 5) hs)
      have hG : P s ∈ Gamma := by
        change L.symm (P s, c) ∈ S
        rw [← (hAc s hsR).2]
        exact (hAgraph (s, c) (hAc s hsR).1).mpr (by change c = c + Q s; rw [hQ, add_zero])
      refine ⟨hG, ⟨s, hs, rfl⟩, ?_⟩
      intro hm
      rw [(hgeom' 4 (by omega)).2.2] at hm
      obtain ⟨t, ht, heq⟩ := hm
      have hts := P.injOn (hPsource (hBR 4 (by omega) ht)) (hPsource hsR) heq
      exact hsnot (hts ▸ ht)
  have hOoutside (x : E2) (hx : x ∈ V 5 \ closure (V 4)) : x ∉ V 3 :=
    fun hm => hx.2 (subset_closure (hmono 3 4 (by omega) (by omega) hm))
  have hproduct : Snew ∩ (L.symm '' O) = L.symm ''
      ((Gamma ∩ (V 5 \ closure (V 4))) ×ˢ Ioo (c - epsilon) (c + epsilon)) := by
    ext y
    constructor
    · rintro ⟨hy, p, hp, rfl⟩
      have hG := (hnewmem p.1 (hOoutside p.1 hp.1) p.2 (hOheight p hp)).mp hy
      exact ⟨p, ⟨⟨hG, hp.1⟩, hp.2⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hG, hx⟩, hz⟩, rfl⟩
      have hp : p ∈ O := ⟨hx, hz⟩
      exact ⟨(hnewmem p.1 (hOoutside p.1 hx) p.2 (hOheight p hp)).mpr hG, p, hp, rfl⟩
  exact ⟨F, hF, hsF, KF, LF, hKF, hLF, KV, LV, hKV, hLV, tau, delta, epsilon,
    chi, hchi, hschi, I, Anew, hFs, hunit, hSflow, hCflow, htau, htaub, htracks,
    hdelta, hgap23, hgap34, hgap56, hepsilon, heb, het, hed, her, hmove2,
    hchirange, hchione, hchis, hI, hIsmooth, hIinverse, hIzero, hIheight,
    hCiso, hIsupport, hIfix, hclockmem, hnewmem, hreverse, rfl, hAnewsource,
    hAnewtarget, hAnewsmooth, hAnewinverse, hAnewgraph, hAnewbuffer, hAnewfixed,
    hO, hA6source, hA6target, hA6smooth, hA6inverse, hOtarget, hOinverse, hannulus, hproduct⟩

end PoincareConjecture.M25.Topology3D
