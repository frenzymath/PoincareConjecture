import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceOuterCapFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceOuterGraphFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart









set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_outer_reference_canonical_ball
    (rho : ℝ × ℝ → ℝ)
    (F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hF : ContDiff ℝ ∞ (fun p : E2 × ℝ => F p.2 p.1))
    (hFi : ContDiff ℝ ∞ (fun p : E2 × ℝ => (F p.2).symm p.1))
    (hroot : ∀ theta ∈ Ioo (-3 / 2 : ℝ) (3 / 2),
      ∀ a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
        Real.sqrt 15 / 4 < rho (theta, a) ∧
        rho (theta, a) < Real.sqrt 4095 / 64 ∧
        rho (theta, a) ^ 2 + Real.sqrt (1 - rho (theta, a) ^ 2) +
          rho (theta, a) * theta / 32 = a)
    (himages : ∀ a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
      F a '' ball (0 : E2) 1 = {v : E2 | ‖v‖ < rho (v 0 / ‖v‖, a)} ∧
      F a '' closedBall (0 : E2) 1 = {v : E2 | ‖v‖ ≤ rho (v 0 / ‖v‖, a)} ∧
      F a '' sphere (0 : E2) 1 = {v : E2 | ‖v‖ = rho (v 0 / ‖v‖, a)})
    (h lambda d : ℝ) (hh : |h - 17 / 16| ≤ 1 / 32768)
    (hlambda : 0 < lambda) (hsmall : lambda < 1 / 131072)
    (g D : E2 → ℝ) (hD : ContDiff ℝ ∞ D) (hcD : HasCompactSupport D)
    (hsD : tsupport D ⊆ F h '' ball (0 : E2) 1)
    (hDgraph : ∀ v ∈ F h '' closedBall (0 : E2) 1,
      D v = g v - (‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32))
    (hg : ∀ v ∈ F h '' closedBall (0 : E2) 1,
      h ≤ g v ∧ g v ≤ h + lambda)
    (hgstrict : ∀ v ∈ F h '' ball (0 : E2) 1, h < g v) :
    let C := heightCoordinates
    let M := stackCapProfilePath
      (stackCanonicalHorizontal (1 / 4) (1 / 2))
      (stackCanonicalHorizontal (1 / 4) (1 / 2))
      (stackCanonicalVertical (1 / 4) (1 / 2))
      (stackCanonicalVertical (1 / 4) (1 / 2)) 0
    let N : UnitTwoSphere → E2 × ℝ := fun q =>
      let m := M (C (q : E3))
      (F (h + lambda * m.2) m.1, h + lambda * m.2)
    let Qplus : Set UnitTwoSphere := {q | 0 ≤ (C (q : E3)).2}
    let B : Set E2 := F h '' closedBall (0 : E2) 1
    let cap : UnitTwoSphere → E3 := fun q => C.symm ((N q).1, (N q).2 + d)
    let retained : Set UnitTwoSphere :=
      {q | let p := C (q : E3)
        p.2 ≤ 0 ∨ rho (p.1 0 / ‖p.1‖, h) ≤ ‖p.1‖}
    let E : Set E3 := (fun q : UnitTwoSphere =>
      nestedReferenceDiffeomorph d (q : E3)) '' retained
    N '' Qplus = (fun v : E2 => (v, g v)) '' B →
    ∃ T : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) (E2 × ℝ) E3 ∞,
      (∀ p : E2 × ℝ, T p = C.symm (F (p.2 - d) p.1, p.2)) ∧
      (∀ y : E3, T.symm y = ((F ((C y).2 - d)).symm (C y).1, (C y).2)) ∧
      (∀ q : UnitTwoSphere, cap q =
        T ((M (C (q : E3))).1, h + d + lambda * (M (C (q : E3))).2)) ∧
      ∃ Phi : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
          (E2 × ℝ) (E2 × ℝ) ∞,
        let Psi := C.toDiffeomorph.trans (Phi.trans C.symm.toDiffeomorph)
        let A := (nestedReferenceBallChart d).mapDiffeomorph Psi
        HasCompactSupport (fun p : E2 × ℝ => Phi p - p) ∧
        HasCompactSupport (fun p : E2 × ℝ => Phi.symm p - p) ∧
        (∀ p : E2 × ℝ, (Phi p).1 = p.1 ∧ (Phi.symm p).1 = p.1) ∧
        A.chart.source = univ ∧ A.chart.target = univ ∧
        (∀ y : E3, A.chart y = Psi (nestedReferenceDiffeomorph d y)) ∧
        (∀ y : E3, A.chart.symm y = (nestedReferenceDiffeomorph d).symm (Psi.symm y)) ∧
        E ⊆ (nestedReferenceBallChart d).boundary ∩ {y : E3 | (C y).2 ≤ h + d} ∧
        (∀ y ∈ E, Psi y = y ∧ Psi.symm y = y) ∧
        A.boundary = E ∪ cap '' Qplus ∧
        E ∩ (cap '' Qplus) = T '' (sphere (0 : E2) 1 ×ˢ ({h + d} : Set ℝ)) ∧
        (∀ q ∈ retained,
          A.chart (q : E3) = nestedReferenceDiffeomorph d (q : E3)) ∧
        (∀ q : UnitTwoSphere, -1 / 8 < (C (q : E3)).2 →
          let v := (N q).1
          let p : E3 := C.symm (v, Real.sqrt (1 - ‖v‖ ^ 2))
          ‖p‖ = 1 ∧ A.chart p = cap q) ∧
        ∀ a ∈ Icc (h - 1 / 131072) h,
          A.inside ∩ {y : E3 | (C y).2 = a + d} =
            T '' (ball (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
          A.closedRegion ∩ {y : E3 | (C y).2 = a + d} =
            T '' (closedBall (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
          A.boundary ∩ {y : E3 | (C y).2 = a + d} =
            T '' (sphere (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) := by
  classical
  dsimp only
  let C := heightCoordinates
  let M := stackCapProfilePath
    (stackCanonicalHorizontal (1 / 4) (1 / 2)) (stackCanonicalHorizontal (1 / 4) (1 / 2))
    (stackCanonicalVertical (1 / 4) (1 / 2)) (stackCanonicalVertical (1 / 4) (1 / 2)) 0
  let N : UnitTwoSphere → E2 × ℝ := fun q =>
    let m := M (C (q : E3))
    (F (h + lambda * m.2) m.1, h + lambda * m.2)
  let Qplus : Set UnitTwoSphere := {q | 0 ≤ (C (q : E3)).2}
  let B : Set E2 := F h '' closedBall (0 : E2) 1
  let Dh : Set E2 := F h '' ball (0 : E2) 1
  let cap : UnitTwoSphere → E3 := fun q => C.symm ((N q).1, (N q).2 + d)
  let retained : Set UnitTwoSphere := {q | (C (q : E3)).2 ≤ 0 ∨
    rho ((C (q : E3)).1 0 / ‖(C (q : E3)).1‖, h) ≤ ‖(C (q : E3)).1‖}
  let E : Set E3 := (fun q : UnitTwoSphere => nestedReferenceDiffeomorph d (q : E3)) '' retained
  intro hcap
  change N '' Qplus = (fun v : E2 => (v, g v)) '' B at hcap
  let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
  let theta : E2 → ℝ := fun v => v 0 / ‖v‖
  let U : E2 → ℝ := fun v => ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let L : E2 → ℝ := fun v => ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let R : ℝ → ℝ → ℝ := fun t r => r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
  obtain ⟨hr0, _, hr1, _, _, hEst⟩ := radial_estimates
  have hhJ : h ∈ J := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hh
    constructor <;> linarith only [hlo, hhi]
  have hnorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hangle (v : E2) : theta v ∈ Ioo (-3 / 2 : ℝ) (3 / 2) ∧
      ‖v‖ * theta v = v 0 := by
    have hc : -‖v‖ ≤ v 0 ∧ v 0 ≤ ‖v‖ := by
      constructor <;> nlinarith only [hnorm v, norm_nonneg v, sq_nonneg (v 1)]
    by_cases hz : ‖v‖ = 0
    · have hv := norm_eq_zero.mp hz
      subst v
      norm_num [theta]
    · have hp := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hz)
      have ht : -1 ≤ theta v ∧ theta v ≤ 1 := by
        constructor
        · exact (le_div_iff₀ hp).mpr (by simpa using hc.1)
        · exact (div_le_iff₀ hp).mpr (by simpa using hc.2)
      exact ⟨⟨by linarith only [ht.1], by linarith only [ht.2]⟩,
        mul_div_cancel₀ _ hz⟩
  have hR (v : E2) : R (theta v) ‖v‖ = U v := by
    dsimp only [R, U]
    rw [(hangle v).2]
  have hRoots (v : E2) (a : ℝ) (ha : a ∈ J) := hroot (theta v) (hangle v).1 a ha
  have hAnti (v : E2) : StrictAntiOn (R (theta v)) (Icc (Real.sqrt 15 / 4) 1) :=
    (hEst (theta v) (hangle v).1).2.2.2.2.2.2.1
  have hRootMem (v : E2) (a : ℝ) (ha : a ∈ J) :
      rho (theta v, a) ∈ Icc (Real.sqrt 15 / 4) 1 :=
    ⟨(hRoots v a ha).1.le, ((hRoots v a ha).2.1.trans hr1).le⟩
  have hRootEq (v : E2) (a : ℝ) (ha : a ∈ J) :
      R (theta v) (rho (theta v, a)) = a := (hRoots v a ha).2.2
  have hOrder (v : E2) (a b : ℝ) (ha : a ∈ J) (hb : b ∈ J) :
      (a ≤ b ↔ rho (theta v, b) ≤ rho (theta v, a)) ∧
      (a < b ↔ rho (theta v, b) < rho (theta v, a)) := by
    simpa only [hRootEq v a ha, hRootEq v b hb] using
      And.intro ((hAnti v).le_iff_ge (hRootMem v a ha) (hRootMem v b hb))
        ((hAnti v).lt_iff_gt (hRootMem v a ha) (hRootMem v b hb))
  have hOuter (v : E2) (a : ℝ) (ha : a ∈ J)
      (hv : ‖v‖ ∈ Icc (Real.sqrt 15 / 4) 1) :
      (a < U v ↔ ‖v‖ < rho (theta v, a)) ∧
      (a ≤ U v ↔ ‖v‖ ≤ rho (theta v, a)) ∧
      (U v ≤ a ↔ rho (theta v, a) ≤ ‖v‖) := by
    simpa only [hR, hRootEq v a ha] using
      And.intro ((hAnti v).lt_iff_gt (hRootMem v a ha) hv)
        (And.intro ((hAnti v).le_iff_ge (hRootMem v a ha) hv)
          ((hAnti v).le_iff_ge hv (hRootMem v a ha)))
  have hDh (v : E2) : v ∈ Dh ↔ ‖v‖ < rho (theta v, h) := by
    change v ∈ F h '' ball (0 : E2) 1 ↔ _
    rw [(himages h hhJ).1]; rfl
  have hB (v : E2) : v ∈ B ↔ ‖v‖ ≤ rho (theta v, h) := by
    change v ∈ F h '' closedBall (0 : E2) 1 ↔ _
    rw [(himages h hhJ).2.1]; rfl
  have hBrad : B ⊆ ball (0 : E2) (Real.sqrt 4095 / 64) := fun v hv =>
    mem_ball_zero_iff.mpr (((hB v).mp hv).trans_lt (hRoots v h hhJ).2.1)
  have hB1 (v : E2) (hv : v ∈ B) : ‖v‖ < 1 :=
    (mem_ball_zero_iff.mp (hBrad hv)).trans hr1
  have hDhB : Dh ⊆ B := image_mono ball_subset_closedBall
  have hLbound (v : E2) (hv : ‖v‖ ≤ 1) : L v ≤ 33 / 32 := by
    have hc : v 0 ≤ 1 := by nlinarith only [hnorm v, hv, norm_nonneg v, sq_nonneg (v 1)]
    dsimp only [L]
    nlinarith only [hc, hv, norm_nonneg v, Real.sqrt_nonneg (1 - ‖v‖ ^ 2)]
  have hFshift : ContDiff ℝ ∞ (fun p : ℝ × E2 => F (p.1 - d) p.2) :=
    hF.comp (contDiff_snd.prodMk (contDiff_fst.sub contDiff_const))
  have hFishift : ContDiff ℝ ∞ (fun p : ℝ × E2 => (F (p.1 - d)).symm p.2) :=
    hFi.comp (contDiff_snd.prodMk (contDiff_fst.sub contDiff_const))
  let T := (planarFamilyGraphDiffeomorph (fun a => F (a - d)) hFshift hFishift).trans
    C.symm.toDiffeomorph
  have hT (p : E2 × ℝ) : T p = C.symm (F (p.2 - d) p.1, p.2) := rfl
  have hTflat (a : ℝ) (v : E2) : T (v, a + d) = C.symm (F a v, a + d) := by
    rw [hT, add_sub_cancel_right]
  have hNative (q : UnitTwoSphere) : cap q =
      T ((M (C (q : E3))).1, h + d + lambda * (M (C (q : E3))).2) := by
    have he : h + d + lambda * (M (C (q : E3))).2 - d =
        h + lambda * (M (C (q : E3))).2 := by ring
    rw [hT, he]
    dsimp only [cap, N]
    apply congrArg C.symm
    apply Prod.ext
    · rfl
    · ring
  obtain ⟨V, K, Vbound, hK, hVbound, hV, hsV, _hPhis, _hPhiis, _hzero, _hinverse,
      hSupport, hFix, hHoriz, hLow, hTrack, _hMono, hFib⟩ :=
    exists_outer_reference_graph_flow (F h) g D hD hcD hsD hBrad
      h lambda d hh hlambda hsmall hDgraph hg
  let Phi := clockEvolutionDiffeomorph V hK hVbound hV hsV 0 1
  let Psi := C.toDiffeomorph.trans (Phi.trans C.symm.toDiffeomorph)
  let A := (nestedReferenceBallChart d).mapDiffeomorph Psi
  have hPsiC (y : E3) : C (Psi y) = Phi (C y) := C.apply_symm_apply _
  have hPsiiC (y : E3) : C (Psi.symm y) = Phi.symm (C y) := C.apply_symm_apply _
  have hPhiH (p : E2 × ℝ) : (Phi p).1 = p.1 ∧ (Phi.symm p).1 = p.1 := hHoriz 1 p
  have hPhiLow (v : E2) : Phi (v, L v + d) = (v, L v + d) ∧
      Phi.symm (v, L v + d) = (v, L v + d) := hLow 1 v
  have hPhiUpper (v : E2) (hv : v ∈ B) : Phi (v, U v + d) = (v, g v + d) := by
    have ht := hTrack 1 v
    change Phi (v, U v + d) = (v, U v + d + Real.smoothTransition 1 * D v) at ht
    rw [ht, Real.smoothTransition.one, one_mul, hDgraph v hv]
    congr 1
    dsimp only [U]
    ring
  have hPhiOutside (v : E2) (hv : v ∉ Dh) (z : ℝ) :
      Phi (v, z) = (v, z) ∧ Phi.symm (v, z) = (v, z) :=
    hFix 1 (v, z) (fun hp => hv hp.1)
  have hChart (y : E3) : A.chart y = Psi (nestedReferenceDiffeomorph d y) := rfl
  have hCharti (y : E3) : A.chart.symm y =
      (nestedReferenceDiffeomorph d).symm (Psi.symm y) := rfl
  have hShear (y : E3) : C (nestedReferenceDiffeomorph d y) =
      ((C y).1, (C y).2 + ‖(C y).1‖ ^ 2 + (C y).1 0 / 32 + d) := by
    rw [(nestedReferenceDiffeomorph_apply_symm d).1 y]
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · change y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d = _
      rw [hnorm]
      change y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d =
        y 2 + ((y 0) ^ 2 + (y 1) ^ 2) + y 0 / 32 + d
      ring
  have hSphere (q : UnitTwoSphere) : ‖(C (q : E3)).1‖ ≤ 1 ∧
      ((C (q : E3)).2) ^ 2 = 1 - ‖(C (q : E3)).1‖ ^ 2 := by
    have hq := heightCoordinates_norm_sq (q : E3)
    rw [norm_eq_of_mem_sphere q] at hq
    constructor <;> nlinarith only [hq, norm_nonneg (C (q : E3)).1,
      sq_nonneg (C (q : E3)).2]
  have hUpper (q : UnitTwoSphere) (hq : 0 ≤ (C (q : E3)).2) :
      C (nestedReferenceDiffeomorph d (q : E3)) =
        ((C (q : E3)).1, U (C (q : E3)).1 + d) := by
    have he : (C (q : E3)).2 = Real.sqrt (1 - ‖(C (q : E3)).1‖ ^ 2) := by
      rw [← (hSphere q).2, Real.sqrt_sq hq]
    rw [hShear, he]
    congr 1
    dsimp only [U]
    ring
  have hLower (q : UnitTwoSphere) (hq : (C (q : E3)).2 ≤ 0) :
      C (nestedReferenceDiffeomorph d (q : E3)) =
        ((C (q : E3)).1, L (C (q : E3)).1 + d) := by
    have he : (C (q : E3)).2 = -Real.sqrt (1 - ‖(C (q : E3)).1‖ ^ 2) := by
      rw [← (hSphere q).2, Real.sqrt_sq_eq_abs, abs_of_nonpos hq, neg_neg]
    rw [hShear, he]
    congr 1
    dsimp only [L]
    ring
  let up : E2 → E3 := fun v => C.symm (v, Real.sqrt (1 - ‖v‖ ^ 2))
  have hUpNorm (v : E2) (hv : ‖v‖ ≤ 1) : ‖up v‖ = 1 := by
    have hs : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith only [hv, norm_nonneg v]
    have hn : ‖up v‖ ^ 2 = 1 := by
      rw [heightCoordinates_symm_norm_sq, Real.sq_sqrt hs]
      ring
    nlinarith only [hn, norm_nonneg (up v)]
  have hUpShear (v : E2) : nestedReferenceDiffeomorph d (up v) = C.symm (v, U v + d) := by
    apply C.injective
    rw [hShear, C.apply_symm_apply, C.apply_symm_apply]
    apply Prod.ext
    · rfl
    · dsimp only [U]
      ring
  have hUpChart (v : E2) (hv : v ∈ B) : A.chart (up v) = C.symm (v, g v + d) := by
    rw [hChart, hUpShear]
    change C.symm (Phi (C (C.symm (v, U v + d)))) = _
    rw [C.apply_symm_apply, hPhiUpper v hv]
  have hEdata (y : E3) (hy : y ∈ E) :
      y ∈ (nestedReferenceBallChart d).boundary ∧ (C y).2 ≤ h + d ∧
      Psi y = y ∧ Psi.symm y = y := by
    obtain ⟨q, hq, rfl⟩ := hy
    refine ⟨⟨(q : E3), q.property, rfl⟩, ?_⟩
    by_cases hlow : (C (q : E3)).2 ≤ 0
    · have he := hLower q hlow
      refine ⟨?_, C.injective ?_, C.injective ?_⟩
      · rw [he]
        have hb := hLbound _ (hSphere q).1
        have hhlo := (abs_le.mp hh).1
        dsimp only
        linarith only [hb, hhlo]
      · rw [hPsiC, he]
        exact (hPhiLow _).1
      · rw [hPsiiC, he]
        exact (hPhiLow _).2
    · have hr : rho (theta (C (q : E3)).1, h) ≤ ‖(C (q : E3)).1‖ := hq.resolve_left hlow
      have hn : (C (q : E3)).1 ∉ Dh := fun hv =>
        (not_lt_of_ge hr) ((hDh _).mp hv)
      have he := hUpper q (le_of_not_ge hlow)
      have hu : U (C (q : E3)).1 ≤ h :=
        (hOuter _ h hhJ ⟨(hRoots _ h hhJ).1.le.trans hr, (hSphere q).1⟩).2.2.mpr hr
      refine ⟨?_, C.injective ?_, C.injective ?_⟩
      · rw [he]
        dsimp only
        linarith only [hu]
      · rw [hPsiC, he]
        exact (hPhiOutside _ hn _).1
      · rw [hPsiiC, he]
        exact (hPhiOutside _ hn _).2
  have hRetained (q : UnitTwoSphere) (hq : q ∈ retained) :
      A.chart (q : E3) = nestedReferenceDiffeomorph d (q : E3) := by
    rw [hChart]
    exact (hEdata _ ⟨q, hq, rfl⟩).2.2.1
  have hcapImage : cap '' Qplus = (fun v : E2 => C.symm (v, g v + d)) '' B := by
    let addD : E2 × ℝ → E3 := fun p => C.symm (p.1, p.2 + d)
    change (addD ∘ N) '' Qplus = (addD ∘ fun v : E2 => (v, g v)) '' B
    rw [image_comp, hcap, image_comp]
  have hBoundary : A.boundary = E ∪ cap '' Qplus := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      let q : UnitTwoSphere := ⟨x, hx⟩
      by_cases hq : q ∈ retained
      · left
        rw [hRetained q hq]
        exact ⟨q, hq, rfl⟩
      · have hn : 0 < (C (q : E3)).2 ∧ ‖(C (q : E3)).1‖ < rho (theta (C (q : E3)).1, h) := by
          simpa only [retained, mem_ofPred_eq, not_or, not_le] using hq
        have hv : (C (q : E3)).1 ∈ B := hDhB ((hDh _).mpr hn.2)
        right
        rw [hcapImage]
        refine ⟨(C (q : E3)).1, hv, ?_⟩
        rw [hChart]
        change C.symm (_, _) = C.symm (Phi (C (nestedReferenceDiffeomorph d (q : E3))))
        rw [hUpper q hn.1.le, hPhiUpper _ hv]
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨q, hq, rfl⟩ := hy
        exact ⟨(q : E3), q.property, hRetained q hq⟩
      · rw [hcapImage] at hy
        obtain ⟨v, hv, rfl⟩ := hy
        exact ⟨up v, mem_sphere_zero_iff_norm.mpr (hUpNorm v (hB1 v hv).le), hUpChart v hv⟩
  have hOldRegions (v : E2) (z : ℝ) :
      (C.symm (v, z) ∈ (nestedReferenceBallChart d).inside ↔
        ‖v‖ < 1 ∧ L v + d < z ∧ z < U v + d) ∧
      (C.symm (v, z) ∈ (nestedReferenceBallChart d).closedRegion ↔
        ‖v‖ ≤ 1 ∧ L v + d ≤ z ∧ z ≤ U v + d) := by
    let y := C.symm (v, z)
    have hy0 : y 0 = v 0 := by dsimp only [y, C]; rw [heightCoordinates_symm_apply]; rfl
    have hy1 : y 1 = v 1 := by dsimp only [y, C]; rw [heightCoordinates_symm_apply]; rfl
    have hy2 : y 2 = z := by dsimp only [y, C]; rw [heightCoordinates_symm_apply]; rfl
    have hsum : (y 0) ^ 2 + (y 1) ^ 2 = ‖v‖ ^ 2 := by rw [hy0, hy1, hnorm]
    have hres : y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d =
        z - ‖v‖ ^ 2 - v 0 / 32 - d := by rw [hy0, hy1, hy2, hnorm]; ring
    have hold := (nestedReferenceBallChart_regions d).2.2.2 y
    rw [hsum, hres] at hold
    rw [hold.1, hold.2.1]
    let s := Real.sqrt (1 - ‖v‖ ^ 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 (hv : ‖v‖ ≤ 1) : s ^ 2 = 1 - ‖v‖ ^ 2 :=
      Real.sq_sqrt (by nlinarith only [hv, norm_nonneg v])
    have heq : L v = ‖v‖ ^ 2 - s + v 0 / 32 ∧ U v = ‖v‖ ^ 2 + s + v 0 / 32 := ⟨rfl, rfl⟩
    rw [heq.1, heq.2]
    constructor <;> constructor
    · intro hp
      have hv : ‖v‖ < 1 := by
        nlinarith only [hp, norm_nonneg v, sq_nonneg (z - ‖v‖ ^ 2 - v 0 / 32 - d)]
      refine ⟨hv, ?_, ?_⟩ <;> nlinarith only [hp, hs0, hs2 hv.le]
    · rintro ⟨hv, hlo, hhi⟩
      have hp := mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hhi)
      nlinarith only [hp, hs2 hv.le]
    · intro hp
      have hv : ‖v‖ ≤ 1 := by
        nlinarith only [hp, norm_nonneg v, sq_nonneg (z - ‖v‖ ^ 2 - v 0 / 32 - d)]
      refine ⟨hv, ?_, ?_⟩ <;> nlinarith only [hp, hs0, hs2 hv]
    · rintro ⟨hv, hlo, hhi⟩
      have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
      nlinarith only [hp, hs2 hv]
  have hImage (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (S : Set E3) (y : E3) :
      y ∈ G '' S ↔ G.symm y ∈ S := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [G.symm_apply_apply] using hx
    · exact fun hy => ⟨G.symm y, hy, G.apply_symm_apply y⟩
  have hTransport (v : E2) (z : ℝ) :
      (C.symm (v, z) ∈ A.inside ↔ C.symm (Phi.symm (v, z)) ∈ (nestedReferenceBallChart d).inside) ∧
      (C.symm (v, z) ∈ A.closedRegion ↔
        C.symm (Phi.symm (v, z)) ∈ (nestedReferenceBallChart d).closedRegion) := by
    constructor
    · rw [show A.inside = Psi '' (nestedReferenceBallChart d).inside from
        (nestedReferenceBallChart d).mapDiffeomorph_inside Psi, hImage]
      change C.symm (Phi.symm (C (C.symm (v, z)))) ∈ _ ↔ _
      rw [C.apply_symm_apply]
    · rw [show A.closedRegion = Psi '' (nestedReferenceBallChart d).closedRegion from
        (nestedReferenceBallChart d).mapDiffeomorph_closedRegion Psi, hImage]
      change C.symm (Phi.symm (C (C.symm (v, z)))) ∈ _ ↔ _
      rw [C.apply_symm_apply]
  have hInB (v : E2) (hv : v ∈ B) (z : ℝ) :
      (C.symm (v, z) ∈ A.inside ↔ L v + d < z ∧ z < g v + d) ∧
      (C.symm (v, z) ∈ A.closedRegion ↔ L v + d ≤ z ∧ z ≤ g v + d) := by
    have hpre (S : Set (E2 × ℝ)) : Phi.symm (v, z) ∈ S ↔ (v, z) ∈ Phi '' S := by
      constructor
      · exact fun hy => ⟨Phi.symm (v, z), hy, Phi.apply_symm_apply (v, z)⟩
      · rintro ⟨p, hp, he⟩
        simpa only [← he, Phi.symm_apply_apply] using hp
    have hcc := (hpre ({v} ×ˢ Icc (L v + d) (U v + d))).trans
      (Iff.of_eq (congrArg (fun S => (v, z) ∈ S) (hFib v hv).1))
    have hoo := (hpre ({v} ×ˢ Ioo (L v + d) (U v + d))).trans
      (Iff.of_eq (congrArg (fun S => (v, z) ∈ S) (hFib v hv).2))
    simp only [mem_prod, mem_singleton_iff, (hPhiH (v, z)).2, true_and] at hcc hoo
    have hold := hOldRegions (Phi.symm (v, z)).1 (Phi.symm (v, z)).2
    simp only [Prod.eta] at hold
    rw [(hPhiH (v, z)).2] at hold
    simp only [hB1 v hv, (hB1 v hv).le, true_and] at hold
    exact ⟨(hTransport v z).1.trans (hold.1.trans hoo),
      (hTransport v z).2.trans (hold.2.trans hcc)⟩
  have hOutside (v : E2) (hv : v ∉ Dh) (z : ℝ) :
      (C.symm (v, z) ∈ A.inside ↔ C.symm (v, z) ∈ (nestedReferenceBallChart d).inside) ∧
      (C.symm (v, z) ∈ A.closedRegion ↔
        C.symm (v, z) ∈ (nestedReferenceBallChart d).closedRegion) := by
    simpa only [(hPhiOutside v hv z).2] using hTransport v z
  have hCutBounds (a : ℝ) (ha : a ∈ Icc (h - 1 / 131072) h) : a ∈ J ∧ 33 / 32 < a := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hh
    exact ⟨⟨by linarith only [ha.1, hlo], by linarith only [ha.2, hhi]⟩,
      by linarith only [ha.1, hlo]⟩
  have hCutTests (a : ℝ) (ha : a ∈ Icc (h - 1 / 131072) h) (v : E2) :
      (C.symm (v, a + d) ∈ A.inside ↔ ‖v‖ < rho (theta v, a)) ∧
      (C.symm (v, a + d) ∈ A.closedRegion ↔ ‖v‖ ≤ rho (theta v, a)) := by
    have haJ := (hCutBounds a ha).1
    have hbelow (hv : ‖v‖ ≤ 1) : L v + d < a + d := by
      linarith only [hLbound v hv, (hCutBounds a ha).2]
    by_cases hv : v ∈ Dh
    · have hvB := hDhB hv
      have hr := ((hDh v).mp hv).trans_le ((hOrder v a h haJ hhJ).1.mp ha.2)
      have hu : a + d < g v + d := by linarith only [ha.2, hgstrict v hv]
      rw [(hInB v hvB (a + d)).1, (hInB v hvB (a + d)).2]
      exact ⟨⟨fun _ => hr, fun _ => ⟨hbelow (hB1 v hvB).le, hu⟩⟩,
        ⟨fun _ => hr.le, fun _ => ⟨(hbelow (hB1 v hvB).le).le, hu.le⟩⟩⟩
    · have hvr : rho (theta v, h) ≤ ‖v‖ := le_of_not_gt (fun hr => hv ((hDh v).mpr hr))
      have hr0v := (hRoots v h hhJ).1.le.trans hvr
      rw [(hOutside v hv (a + d)).1, (hOutside v hv (a + d)).2,
        (hOldRegions v (a + d)).1, (hOldRegions v (a + d)).2]
      constructor <;> constructor
      · rintro ⟨hr, _, hu⟩
        exact (hOuter v a haJ ⟨hr0v, hr.le⟩).1.mp (by linarith only [hu])
      · intro hr
        have hr1v := hr.trans ((hRoots v a haJ).2.1.trans hr1)
        exact ⟨hr1v, hbelow hr1v.le,
          by linarith only [(hOuter v a haJ ⟨hr0v, hr1v.le⟩).1.mpr hr]⟩
      · rintro ⟨hr, _, hu⟩
        exact (hOuter v a haJ ⟨hr0v, hr⟩).2.1.mp (by linarith only [hu])
      · intro hr
        have hr1v := hr.trans_lt ((hRoots v a haJ).2.1.trans hr1)
        exact ⟨hr1v.le, (hbelow hr1v.le).le,
          by linarith only [(hOuter v a haJ ⟨hr0v, hr1v.le⟩).2.1.mpr hr]⟩
  have hBoundaryMem (y : E3) : y ∈ A.boundary ↔ y ∈ A.closedRegion ∧ y ∉ A.inside := by
    constructor
    · intro hy
      refine ⟨?_, fun hi => (Set.disjoint_left.mp A.inside_disjoint_boundary) hi hy⟩
      rw [← A.inside_union_boundary]
      exact Or.inr hy
    · rintro ⟨hy, hn⟩
      rw [← A.inside_union_boundary] at hy
      exact hy.resolve_left hn
  have hSection (S : Set E3) (B0 : Set E2) (a : ℝ)
      (hs : ∀ v : E2, C.symm (v, a + d) ∈ S ↔ v ∈ F a '' B0) :
      S ∩ {y : E3 | (C y).2 = a + d} = T '' (B0 ×ˢ ({a + d} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨hy, hhgt⟩
      have he : C.symm ((C y).1, a + d) = y := by rw [← hhgt, Prod.eta, C.symm_apply_apply]
      obtain ⟨v, hv, heq⟩ := (hs (C y).1).mp (he.symm ▸ hy)
      exact ⟨(v, a + d), ⟨hv, rfl⟩, by rw [hTflat, heq, he]⟩
    · rintro ⟨⟨v, z⟩, ⟨hv, hz⟩, rfl⟩
      change z = a + d at hz
      subst z
      rw [hTflat]
      exact ⟨(hs (F a v)).mpr ⟨v, hv, rfl⟩, by
        change (C (C.symm (F a v, a + d))).2 = a + d
        rw [C.apply_symm_apply]⟩
  have hCuts (a : ℝ) (ha : a ∈ Icc (h - 1 / 131072) h) :
      A.inside ∩ {y : E3 | (C y).2 = a + d} = T '' (ball (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
      A.closedRegion ∩ {y : E3 | (C y).2 = a + d} =
        T '' (closedBall (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ∧
      A.boundary ∩ {y : E3 | (C y).2 = a + d} = T '' (sphere (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) := by
    have haJ := (hCutBounds a ha).1
    refine ⟨hSection A.inside _ a ?_, hSection A.closedRegion _ a ?_, hSection A.boundary _ a ?_⟩
    · intro v
      rw [(himages a haJ).1]
      exact (hCutTests a ha v).1
    · intro v
      rw [(himages a haJ).2.1]
      exact (hCutTests a ha v).2
    · intro v
      rw [(himages a haJ).2.2, hBoundaryMem, (hCutTests a ha v).1, (hCutTests a ha v).2]
      exact ⟨fun hp => le_antisymm hp.1 (le_of_not_gt hp.2),
        fun hp => ⟨hp.le, not_lt_of_ge hp.ge⟩⟩
  have hRim : E ∩ (cap '' Qplus) = T '' (sphere (0 : E2) 1 ×ˢ ({h + d} : Set ℝ)) := by
    apply Subset.antisymm
    · rintro y ⟨hyE, hyN⟩
      have hyb : y ∈ A.boundary := hBoundary.symm ▸ Or.inr hyN
      have hyh := (hEdata y hyE).2.1
      rw [hcapImage] at hyN
      obtain ⟨v, hv, rfl⟩ := hyN
      rw [C.apply_symm_apply] at hyh
      have he : g v + d = h + d := by linarith only [hyh, (hg v hv).1]
      exact (hCuts h ⟨by linarith, le_rfl⟩).2.2 ▸ ⟨hyb, by
        change (C (C.symm (v, g v + d))).2 = h + d
        rw [C.apply_symm_apply]
        exact he⟩
    · rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
      change z = h + d at hz
      subst z
      rw [hTflat]
      let v := F h x
      have hvB : v ∈ B := ⟨x, sphere_subset_closedBall hx, rfl⟩
      have hr : ‖v‖ = rho (theta v, h) := by
        have hm : v ∈ F h '' sphere (0 : E2) 1 := ⟨x, hx, rfl⟩
        simpa only [(himages h hhJ).2.2, mem_ofPred_eq] using hm
      have hvn : v ∉ Dh := fun hv => (hDh v).mp hv |>.ne hr
      have hUv : U v = h := by
        rw [← hR v, hr]
        exact (hRoots v h hhJ).2.2
      have hgv : g v = h := by
        have he := hDgraph v hvB
        change D v = g v - U v at he
        rw [image_eq_zero_of_notMem_tsupport (fun hv => hvn (hsD hv)), hUv] at he
        linarith only [he]
      let q : UnitTwoSphere := ⟨up v, mem_sphere_zero_iff_norm.mpr (hUpNorm v (hB1 v hvB).le)⟩
      have hq : q ∈ retained := by
        right
        change rho (theta (C (up v)).1, h) ≤ ‖(C (up v)).1‖
        rw [C.apply_symm_apply]
        exact hr.ge
      refine ⟨⟨q, hq, ?_⟩, ?_⟩
      · change nestedReferenceDiffeomorph d (up v) = C.symm (v, h + d)
        rw [hUpShear, hUv]
      · rw [hcapImage]
        exact ⟨v, hvB, by change C.symm (v, g v + d) = C.symm (v, h + d); rw [hgv]⟩
  have hNativePoint (q : UnitTwoSphere) (hq : -1 / 8 < (C (q : E3)).2) :
      ‖up (N q).1‖ = 1 ∧ A.chart (up (N q).1) = cap q := by
    by_cases hp : 0 ≤ (C (q : E3)).2
    · have hm : N q ∈ (fun v : E2 => (v, g v)) '' B := hcap ▸ ⟨q, hp, rfl⟩
      obtain ⟨v, hv, he⟩ := hm
      have hvq : v = (N q).1 := congrArg Prod.fst he
      have hgq : g v = (N q).2 := congrArg Prod.snd he
      rw [← hvq]
      refine ⟨hUpNorm v (hB1 v hv).le, ?_⟩
      rw [hUpChart v hv]
      exact congrArg C.symm (Prod.ext hvq (congrArg (fun z => z + d) hgq))
    · have hw : (C (q : E3)).2 < 0 := lt_of_not_ge hp
      obtain ⟨_, hapos, _, _, hanear, _, _⟩ := stackCanonicalHorizontal_spec
        (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      obtain ⟨_, _, _, _, hbfar, _⟩ := stackCanonicalVertical_spec
        (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      have habs : |(C (q : E3)).2| ≤ 1 / 4 := by
        rw [abs_of_neg hw]
        linarith only [hq]
      have hs : Real.sqrt (1 - ((C (q : E3)).2) ^ 2) = ‖(C (q : E3)).1‖ := by
        rw [show 1 - ((C (q : E3)).2) ^ 2 = ‖(C (q : E3)).1‖ ^ 2 by
          linarith only [(hSphere q).2], Real.sqrt_sq (norm_nonneg _)]
      have hpos : 0 < ‖(C (q : E3)).1‖ := by
        nlinarith only [(hSphere q).2, norm_nonneg (C (q : E3)).1, hw, hq]
      have hmodel : ‖(M (C (q : E3))).1‖ = 1 ∧ (M (C (q : E3))).2 = (C (q : E3)).2 := by
        have hblend (f : E2 → ℝ) (x : E2) : stackProfileBlend f f 0 x = f x :=
          stackProfileBlend_of_nonpos f f 0 le_rfl x
        have han := hanear (C (q : E3)).2 habs
        have hm1 : (M (C (q : E3))).1 =
            stackCanonicalHorizontal (1 / 4) (1 / 2) (C (q : E3)).2 • (C (q : E3)).1 := by
          simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos _ _ 0 le_rfl]
        have hmn : ‖(M (C (q : E3))).1‖ = 1 := by
          rw [hm1, norm_smul, Real.norm_eq_abs, abs_of_pos (hapos _), han, hs,
            inv_mul_cancel₀ hpos.ne']
        refine ⟨hmn, ?_⟩
        change stackProfileBlend _ _ 0 (M (C (q : E3))).1 * (C (q : E3)).2 = _
        rw [hblend, hbfar _ (by rw [hmn]; norm_num), one_mul]
      let a := h + lambda * (C (q : E3)).2
      have haJ : a ∈ J := by
        obtain ⟨hlo, hhi⟩ := abs_le.mp hh
        have hloP := mul_lt_mul_of_pos_left hq hlambda
        have hhiP := mul_neg_of_pos_of_neg hlambda hw
        constructor <;> dsimp only [a] <;> linarith only [hlo, hhi, hloP, hhiP, hsmall]
      have hah : a < h := by dsimp only [a]; nlinarith only [hlambda, hw]
      have hN : N q = (F a (M (C (q : E3))).1, a) := by
        dsimp only [N, a]
        rw [hmodel.2]
      have hr : ‖(N q).1‖ = rho (theta (N q).1, a) := by
        have hm : (N q).1 ∈ F a '' sphere (0 : E2) 1 :=
          ⟨(M (C (q : E3))).1, mem_sphere_zero_iff_norm.mpr hmodel.1, by rw [hN]⟩
        simpa only [(himages a haJ).2.2, mem_ofPred_eq] using hm
      have hv1 : ‖(N q).1‖ < 1 := hr ▸ (hRoots (N q).1 a haJ).2.1.trans hr1
      have hvn : (N q).1 ∉ Dh := by
        intro hv
        have hlt := (hDh _).mp hv
        have horder := (hOrder (N q).1 a h haJ hhJ).2.mp hah
        linarith only [hlt, horder, hr]
      have hUv : U (N q).1 = a := by
        rw [← hR, hr]
        exact (hRoots (N q).1 a haJ).2.2
      refine ⟨hUpNorm _ hv1.le, ?_⟩
      rw [hChart, hUpShear]
      change C.symm (Phi (C (C.symm ((N q).1, U (N q).1 + d)))) = cap q
      rw [C.apply_symm_apply, (hPhiOutside _ hvn _).1, hUv]
      change C.symm ((N q).1, a + d) = C.symm ((N q).1, (N q).2 + d)
      rw [hN]
  obtain ⟨S, hS, _hSO, hsupp⟩ := hSupport
  refine ⟨T, hT, fun _ => rfl, hNative, Phi,
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp 1).1,
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp 1).2, hPhiH,
    ?_, ?_, hChart, hCharti, fun y hy => ⟨(hEdata y hy).1, (hEdata y hy).2.1⟩,
    fun y hy => (hEdata y hy).2.2, hBoundary, hRim, hRetained, hNativePoint, hCuts⟩
  · ext y
    simp [BallNeighborhoodChart.mapDiffeomorph, nestedReferenceBallChart]
  · ext y
    simp [BallNeighborhoodChart.mapDiffeomorph, nestedReferenceBallChart]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
