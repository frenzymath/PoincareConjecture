import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProduct
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapEnd
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTwoTubeEnds

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackMorseCapMatchedChart
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (C : SurgeryCapTag psi u)
    (A : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hA : ContDiffOn ℝ ∞ A A.source)
    (hAi : ContDiffOn ℝ ∞ A.symm A.target)
    (c kappa rho : ℝ) (hkappa : |kappa| = 1) (hrho : 0 < rho)
    (hsource : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source)
    (hheight : ∀ p ∈ A.source, ⟪(u : E3), A p⟫_ℝ = p.2)
    (hgraph : ∀ p ∈ A.source,
      A p ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        p.2 = c + kappa * ‖p.1‖ ^ 2) :
    let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
    let s : ℝ := c + kappa * rho ^ 2
    let t : ℝ := C.cutHeight + C.sign * C.removal
    let ell : ℝ := min s t
    let upper : ℝ := max s t
    let H : E3 → ℝ × E2 := fun y =>
      ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1)
    let Hinv : ℝ × E2 → E3 := fun p =>
      (heightPlaneCoordinates u).symm (p.2, p.1)
    0 < kappa * (t - s) →
    ∀ eta : ℝ, 0 < eta →
    ∀ gamma : ℝ → UnitCircle → E2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => gamma p.1 p.2) →
      (∀ z ∈ Icc (ell - eta) (upper + eta),
        IsPlanarEmbedding (gamma z)) →
      (∀ z ∈ Icc (ell - eta) (upper + eta),
        range (gamma z) = {x : E2 | Hinv (z, x) ∈ S}) →
      ∃ epsilon delta : ℝ,
        0 < epsilon ∧ 4 * epsilon < eta ∧
        4 * epsilon < rho ^ 2 / 4 ∧
        4 * epsilon < C.scale * C.overlapWidth / 2 ∧
        8 * epsilon < upper - ell ∧ 0 < delta ∧ delta < 1 / 4 ∧
        ∃ RM RC : E2 ≃ₗᵢ[ℝ] E2,
          ∃ T Q : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2),
            T.source = {p : ℝ × E2 |
              0 < kappa * (p.1 - c) ∧
                (Real.sqrt (kappa * (p.1 - c)) • RM p.2, p.1) ∈ A.source} ∧
            T.target = {p : ℝ × E2 |
              Hinv p ∈ A.target ∧ 0 < kappa * (p.1 - c)} ∧
            (∀ p : ℝ × E2,
              T p = H (A (Real.sqrt (kappa * (p.1 - c)) • RM p.2, p.1))) ∧
            (∀ p ∈ T.target,
              T.symm p = (p.1, RM.symm
                ((Real.sqrt (kappa * (p.1 - c)))⁻¹ •
                  (A.symm (Hinv p)).1))) ∧
            ContDiffOn ℝ ∞ T T.source ∧
            ContDiffOn ℝ ∞ T.symm T.target ∧
            (∀ p ∈ T.source, (T p).1 = p.1) ∧
            (∀ p ∈ T.target, (T.symm p).1 = p.1) ∧
            Icc (s - 3 * epsilon) (s + 3 * epsilon) ×ˢ
              closedBall (0 : E2) 1 ⊆ T.source ∧
            ContDiffOn ℝ ∞ Q Q.source ∧
            ContDiffOn ℝ ∞ Q.symm Q.target ∧
            (∀ p ∈ Q.source, (Q p).1 = p.1) ∧
            (∀ p ∈ Q.target, (Q.symm p).1 = p.1) ∧
            Icc (ell - eta) (upper + eta) ×ˢ
              closedBall (0 : E2) 1 ⊆ Q.source ∧
            (∀ z ∈ Icc (s - epsilon) (s + epsilon), ∀ x : E2,
              |‖x‖ - 1| < delta →
                (z, x) ∈ Q.source ∧ T (z, x) = Q (z, x)) ∧
            (∀ z ∈ Icc (t - epsilon) (t + epsilon), ∀ x : E2,
              |‖x‖ - 1| < delta →
                (z, x) ∈ Q.source ∧ stackCapEndChart C RC (z, x) = Q (z, x)) ∧
            Hinv '' (Q '' (Icc ell upper ×ˢ sphere (0 : E2) 1)) =
              {y : E3 | y ∈ S ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} := by
  classical
  intro S s t ell upper H Hinv horder eta heta gamma hgamma hge hfull
  have hkcases : kappa = 1 ∨ kappa = -1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using hkappa
  have hpositive (hk : kappa = 1) : ell = s ∧ upper = t := by
    have hst : s < t := by rw [hk, one_mul] at horder; linarith only [horder]
    exact ⟨min_eq_left hst.le, max_eq_right hst.le⟩
  have hnegative (hk : kappa ≠ 1) : ell = t ∧ upper = s := by
    have hk' := hkcases.resolve_left hk
    have hts : t < s := by rw [hk', neg_one_mul] at horder; linarith only [horder]
    exact ⟨min_eq_right hts.le, max_eq_left hts.le⟩
  have hlt : ell < upper := by
    by_cases hk : kappa = 1
    · rw [(hpositive hk).1, (hpositive hk).2]
      rw [hk, one_mul] at horder
      linarith only [horder]
    · rw [(hnegative hk).1, (hnegative hk).2]
      rw [hkcases.resolve_left hk, neg_one_mul] at horder
      linarith only [horder]
  have hsBand : s ∈ Icc ell upper := ⟨min_le_left _ _, le_max_left _ _⟩
  have htBand : t ∈ Icc ell upper := ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨wM, hwM, hwMeta, hwMrho, T0, hT0s, hT0t, hT0form,
      hT0, hT0i, hT0filled, _hrad, hT0h, hT0inv, hT0sphere, _hfibers⟩ :=
    exists_stackMorseEndTube psi u A hA hAi c kappa rho eta hkappa hrho heta
      hsource hheight hgraph
  let TC0 := stackCapEndChart C (LinearIsometryEquiv.refl ℝ E2)
  obtain ⟨_hTC0s, _hTC0t, hTC0form, _hTC0inv, hTC0, hTC0i,
      hTC0filled, hTC0h, _hTC0ih⟩ :=
    stackCapEndChart_spec C (LinearIsometryEquiv.refl ℝ E2)
  let wC := min eta (C.scale * C.overlapWidth / 2)
  have hwC : 0 < wC := lt_min heta
    (div_pos (mul_pos C.scale_pos C.overlap_pos) (by norm_num))
  have hwCeta : wC ≤ eta := min_le_left _ _
  have hwCoverlap : wC ≤ C.scale * C.overlapWidth / 2 := min_le_right _ _
  have hMsource : Ioo (s - wM) (s + wM) ×ˢ
      closedBall (0 : E2) 1 ⊆ T0.source := by
    intro p hp
    exact hT0filled ⟨⟨hp.1.1.le, hp.1.2.le⟩,
      closedBall_subset_closedBall (by norm_num) hp.2⟩
  have hCsource : Ioo (t - wC) (t + wC) ×ˢ
      closedBall (0 : E2) 1 ⊆ TC0.source :=
    fun _ hp => hTC0filled ⟨mem_univ _, hp.2⟩
  have hMfamily (z : ℝ) (hz : z ∈ Ioo (s - wM) (s + wM)) :
      z ∈ Icc (ell - eta) (upper + eta) := by
    constructor <;> linarith only [hz.1, hz.2, hwMeta, hsBand.1, hsBand.2]
  have hCfamily (z : ℝ) (hz : z ∈ Ioo (t - wC) (t + wC)) :
      z ∈ Icc (ell - eta) (upper + eta) := by
    constructor <;> linarith only [hz.1, hz.2, hwCeta, htBand.1, htBand.2]
  have hMcircle (z : ℝ) (hz : z ∈ Ioo (s - wM) (s + wM)) (q : UnitCircle) :
      (T0 (z, (q : E2))).2 ∈ range (gamma z) := by
    have hp : (z, (q : E2)) ∈ T0.source :=
      hMsource ⟨hz, sphere_subset_closedBall q.property⟩
    rw [hfull z (hMfamily z hz)]
    change Hinv (z, (T0 (z, (q : E2))).2) ∈ S
    have hh := hT0h (z, (q : E2)) hp
    change (T0 (z, (q : E2))).1 = z at hh
    have hS := (hT0sphere (z, (q : E2)) hp).mpr (norm_eq_of_mem_sphere q)
    simpa only [hh] using hS
  have htube (z : ℝ) (hz : z ∈ Ioo (t - wC) (t + wC)) (theta : UnitCircle) :
      C.tube ((theta : E2), z) ∈ S := by
    let v := (z - t) / (C.sign * C.scale)
    have hsign : C.sign ≠ 0 := by
      intro h
      have h' := C.sign_abs
      rw [h, abs_zero] at h'
      norm_num at h'
    have hv : |v| < C.overlapWidth / 2 := by
      dsimp only [v]
      rw [abs_div, abs_mul, C.sign_abs, one_mul, abs_of_pos C.scale_pos,
        div_lt_iff₀ C.scale_pos]
      rw [abs_lt]
      constructor <;> nlinarith only [hz.1, hz.2, hwCoverlap]
    have hvsmall : |v| < 1 / 4 := by linarith only [hv, C.overlap_le]
    have hv1 : 0 < 1 - v ^ 2 := by
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hvsmall
      nlinarith
    let a := Real.sqrt (1 - v ^ 2)
    have ha : 0 < a := Real.sqrt_pos.mpr hv1
    have hasq : a ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hv1.le
    have hnorm : ‖heightCoordinates.symm (a • (theta : E2), v)‖ = 1 := by
      have hh := heightCoordinates_symm_norm_sq (a • (theta : E2), v)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_eq_of_mem_sphere,
        mul_one, hasq] at hh
      nlinarith [norm_nonneg (heightCoordinates.symm (a • (theta : E2), v))]
    let q : UnitTwoSphere := ⟨heightCoordinates.symm (a • (theta : E2), v),
      mem_sphere_zero_iff_norm.mpr hnorm⟩
    have hcoord : heightCoordinates (q : E3) = (a • (theta : E2), v) :=
      heightCoordinates.apply_symm_apply _
    have hmodel : C.profile.model q = ((theta : E2), v) := by
      have hh := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far q (by rw [hcoord]; exact hvsmall.le)
      change C.profile.model q = _ at hh
      rw [hcoord, circleDirection_smul theta ha] at hh
      exact hh
    have hvheight : C.cutHeight + C.sign * (C.removal + C.scale * v) = z := by
      dsimp [v, t]
      field_simp [hsign, C.scale_pos.ne']
      ring
    refine ⟨C.sourceChart q, ?_⟩
    change psi (C.sourceChart q, 0) = C.tube ((theta : E2), z)
    rw [C.central_eq q (by rw [hcoord]; linarith [le_abs_self v, C.overlap_pos]),
      SurgeryCapProfile.capMap_apply, hmodel, hvheight]
  have hCcircle (z : ℝ) (hz : z ∈ Ioo (t - wC) (t + wC)) (q : UnitCircle) :
      (TC0 (z, (q : E2))).2 ∈ range (gamma z) := by
    have hqsource : ((q : E2), z) ∈ C.tube.source :=
      C.tube_source ⟨sphere_subset_closedBall q.property, mem_univ _⟩
    have hqheight : ⟪(u : E3), C.tube ((q : E2), z)⟫_ℝ = z :=
      C.tube_height ((q : E2), z) hqsource
    rw [hfull z (hCfamily z hz), hTC0form]
    change (heightPlaneCoordinates u).symm
      ((heightPlaneCoordinates u (C.tube ((q : E2), z))).1, z) ∈ S
    rw [heightPlaneCoordinates_reconstruct u _ z hqheight]
    exact htube z hz q
  let Tm0 := if kappa = 1 then T0 else TC0
  let Tp0 := if kappa = 1 then TC0 else T0
  let wm := if kappa = 1 then wM else wC
  let wp := if kappa = 1 then wC else wM
  have hTm0 : ContDiffOn ℝ ∞ Tm0 Tm0.source := by
    by_cases hk : kappa = 1 <;> simp only [Tm0, hk, ite_true, ite_false] <;> assumption
  have hTm0i : ContDiffOn ℝ ∞ Tm0.symm Tm0.target := by
    by_cases hk : kappa = 1 <;> simp only [Tm0, hk, ite_true, ite_false] <;> assumption
  have hTp0 : ContDiffOn ℝ ∞ Tp0 Tp0.source := by
    by_cases hk : kappa = 1 <;> simp only [Tp0, hk, ite_true, ite_false] <;> assumption
  have hTp0i : ContDiffOn ℝ ∞ Tp0.symm Tp0.target := by
    by_cases hk : kappa = 1 <;> simp only [Tp0, hk, ite_true, ite_false] <;> assumption
  have hTm0h : ∀ p ∈ Tm0.source, (Tm0 p).1 = p.1 := by
    by_cases hk : kappa = 1 <;> simp only [Tm0, hk, ite_true, ite_false] <;> assumption
  have hTp0h : ∀ p ∈ Tp0.source, (Tp0 p).1 = p.1 := by
    by_cases hk : kappa = 1 <;> simp only [Tp0, hk, ite_true, ite_false] <;> assumption
  have hwm : 0 < wm := by
    by_cases hk : kappa = 1 <;> simp only [wm, hk, ite_true, ite_false] <;> assumption
  have hwp : 0 < wp := by
    by_cases hk : kappa = 1 <;> simp only [wp, hk, ite_true, ite_false] <;> assumption
  have hTms : Ioo (ell - wm) (ell + wm) ×ˢ closedBall (0 : E2) 1 ⊆ Tm0.source := by
    by_cases hk : kappa = 1
    · simpa only [Tm0, wm, if_pos hk, (hpositive hk).1] using hMsource
    · simpa only [Tm0, wm, if_neg hk, (hnegative hk).1] using hCsource
  have hTps : Ioo (upper - wp) (upper + wp) ×ˢ closedBall (0 : E2) 1 ⊆ Tp0.source := by
    by_cases hk : kappa = 1
    · simpa only [Tp0, wp, if_pos hk, (hpositive hk).2] using hCsource
    · simpa only [Tp0, wp, if_neg hk, (hnegative hk).2] using hMsource
  have hmcircle : ∀ z ∈ Ioo (ell - wm) (ell + wm), ∀ q : UnitCircle,
      (Tm0 (z, (q : E2))).2 ∈ range (gamma z) := by
    by_cases hk : kappa = 1
    · simpa only [Tm0, wm, if_pos hk, (hpositive hk).1] using hMcircle
    · simpa only [Tm0, wm, if_neg hk, (hnegative hk).1] using hCcircle
  have hpcircle : ∀ z ∈ Ioo (upper - wp) (upper + wp), ∀ q : UnitCircle,
      (Tp0 (z, (q : E2))).2 ∈ range (gamma z) := by
    by_cases hk : kappa = 1
    · simpa only [Tp0, wp, if_pos hk, (hpositive hk).2] using hCcircle
    · simpa only [Tp0, wp, if_neg hk, (hnegative hk).2] using hMcircle
  obtain ⟨epsilon, delta, he, heeta, hewm, hewp, hsep, hd, hdquarter,
      Rm, Rp, _hRm, _hRp, cbar, _hcb, _hcbe, hrange, _hout, D, G,
      Tm, Tp, Q, hmSource, hmTarget, hmValue, hmInverse, hTm, hTmi,
      hTmh, hTmih, hmFilled, hpSource, hpTarget, hpValue, hpInverse,
      hTp, hTpi, hTph, hTpih, hpFilled, _hQt, hQ, hQi, hQh, hQih,
      hQsource, _hQproduct, hQcircle, hmatchm, hmatchp⟩ :=
    exists_stackTwoTubeMatchedChart Tm0 Tp0 hTm0 hTm0i hTp0 hTp0i hTm0h hTp0h
      ell upper wm wp eta hlt hwm hwp heta hTms hTps hP gamma hgamma hge
      hmcircle hpcircle
  let RM := if kappa = 1 then Rm else Rp
  let RC := if kappa = 1 then Rp else Rm
  let T := if kappa = 1 then Tm else Tp
  have heM : 4 * epsilon < wM := by
    by_cases hk : kappa = 1
    · simpa only [wm, if_pos hk] using hewm
    · simpa only [wp, if_neg hk] using hewp
  have heC : 4 * epsilon < wC := by
    by_cases hk : kappa = 1
    · simpa only [wp, if_pos hk] using hewp
    · simpa only [wm, if_neg hk] using hewm
  have hTs : T.source = {p : ℝ × E2 | (p.1, RM p.2) ∈ T0.source} := by
    by_cases hk : kappa = 1
    · simpa only [T, RM, Tm0, if_pos hk] using hmSource
    · simpa only [T, RM, Tp0, if_neg hk] using hpSource
  have hTt : T.target = T0.target := by
    by_cases hk : kappa = 1
    · simpa only [T, Tm0, if_pos hk] using hmTarget
    · simpa only [T, Tp0, if_neg hk] using hpTarget
  have hTv : ∀ p : ℝ × E2, T p = T0 (p.1, RM p.2) := by
    by_cases hk : kappa = 1
    · simpa only [T, RM, Tm0, if_pos hk] using hmValue
    · simpa only [T, RM, Tp0, if_neg hk] using hpValue
  have hTinv : ∀ p : ℝ × E2,
      T.symm p = ((T0.symm p).1, RM.symm (T0.symm p).2) := by
    by_cases hk : kappa = 1
    · simpa only [T, RM, Tm0, if_pos hk] using hmInverse
    · simpa only [T, RM, Tp0, if_neg hk] using hpInverse
  have hT : ContDiffOn ℝ ∞ T T.source := by
    by_cases hk : kappa = 1 <;> simp only [T, hk, ite_true, ite_false] <;> assumption
  have hTi : ContDiffOn ℝ ∞ T.symm T.target := by
    by_cases hk : kappa = 1 <;> simp only [T, hk, ite_true, ite_false] <;> assumption
  have hTh : ∀ p ∈ T.source, (T p).1 = p.1 := by
    by_cases hk : kappa = 1 <;> simp only [T, hk, ite_true, ite_false] <;> assumption
  have hTih : ∀ p ∈ T.target, (T.symm p).1 = p.1 := by
    by_cases hk : kappa = 1 <;> simp only [T, hk, ite_true, ite_false] <;> assumption
  have hTfilled : Icc (s - 3 * epsilon) (s + 3 * epsilon) ×ˢ
      closedBall (0 : E2) 1 ⊆ T.source := by
    by_cases hk : kappa = 1
    · simpa only [T, if_pos hk, (hpositive hk).1] using hmFilled
    · simpa only [T, if_neg hk, (hnegative hk).2] using hpFilled
  have hmatchM : ∀ z ∈ Icc (s - epsilon) (s + epsilon), ∀ x : E2,
      |‖x‖ - 1| < delta → (z, x) ∈ Q.source ∧ T (z, x) = Q (z, x) := by
    intro z hz x hx
    by_cases hk : kappa = 1
    · have hh := hmatchm z (by simpa only [(hpositive hk).1] using hz) x hx
      exact ⟨hh.1, by simpa only [T, if_pos hk] using hh.2.symm⟩
    · have hh := hmatchp z (by simpa only [(hnegative hk).2] using hz) x hx
      exact ⟨hh.1, by simpa only [T, if_neg hk] using hh.2.symm⟩
  have hrotate (R : E2 ≃ₗᵢ[ℝ] E2) (p : ℝ × E2) :
      TC0 (p.1, R p.2) = stackCapEndChart C R p := rfl
  have hmatchC : ∀ z ∈ Icc (t - epsilon) (t + epsilon), ∀ x : E2,
      |‖x‖ - 1| < delta →
        (z, x) ∈ Q.source ∧ stackCapEndChart C RC (z, x) = Q (z, x) := by
    intro z hz x hx
    by_cases hk : kappa = 1
    · have hh := hmatchp z (by simpa only [(hpositive hk).2] using hz) x hx
      refine ⟨hh.1, ?_⟩
      rw [hpValue] at hh
      have heq : TC0 (z, Rp x) = Q (z, x) := by
        simpa only [Tp0, if_pos hk] using hh.2.symm
      simpa only [RC, if_pos hk] using (hrotate Rp (z, x)).symm.trans heq
    · have hh := hmatchm z (by simpa only [(hnegative hk).1] using hz) x hx
      refine ⟨hh.1, ?_⟩
      rw [hmValue] at hh
      have heq : TC0 (z, Rm x) = Q (z, x) := by
        simpa only [Tm0, if_neg hk] using hh.2.symm
      simpa only [RC, if_neg hk] using (hrotate Rm (z, x)).symm.trans heq
  have hband (z : ℝ) (hz : z ∈ Icc ell upper) :
      z ∈ Icc (ell - eta) (upper + eta) := by
    constructor <;> linarith only [hz.1, hz.2, heta]
  have hlevels (z : ℝ) (hz : z ∈ Icc ell upper) :
      range (cbar z) = {x : E2 | Hinv (z, x) ∈ S} :=
    (hrange z).trans (hfull z (hband z hz))
  have hQboundary (z : ℝ) (hz : z ∈ Icc ell upper) (q : UnitCircle) :
      Q (z, (q : E2)) = (z, cbar z q) := by
    rw [hQcircle z q q.property, G.chart_apply, D.chart_boundary z (hband z hz) q]
  have hHheight (p : ℝ × E2) : ⟪(u : E3), Hinv p⟫_ℝ = p.1 := by
    rw [← heightPlaneCoordinates_snd]
    exact congrArg Prod.snd ((heightPlaneCoordinates u).apply_symm_apply (p.2, p.1))
  have hcore : Hinv '' (Q '' (Icc ell upper ×ˢ sphere (0 : E2) 1)) =
      {y : E3 | y ∈ S ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨⟨z, x⟩, ⟨hz, hx⟩, rfl⟩, rfl⟩
      rw [hQboundary z hz ⟨x, hx⟩]
      refine ⟨?_, ?_⟩
      · change cbar z ⟨x, hx⟩ ∈ {x : E2 | Hinv (z, x) ∈ S}
        rw [← hlevels z hz]
        exact ⟨(⟨x, hx⟩ : UnitCircle), rfl⟩
      · rw [hHheight]
        exact hz
    · intro y hy
      let z := ⟪(u : E3), y⟫_ℝ
      let x := (heightPlaneCoordinates u y).1
      have hrepr : Hinv (z, x) = y := heightPlaneCoordinates_reconstruct u y z rfl
      have hx : x ∈ range (cbar z) := by
        rw [hlevels z hy.2]
        change Hinv (z, x) ∈ S
        rw [hrepr]
        exact hy.1
      obtain ⟨q, hq⟩ := hx
      refine ⟨Q (z, (q : E2)), ⟨(z, (q : E2)), ⟨hy.2, q.property⟩, rfl⟩, ?_⟩
      rw [hQboundary z hy.2 q, hq]
      exact hrepr
  refine ⟨epsilon, delta, he, heeta, heM.trans hwMrho, heC.trans_le hwCoverlap,
    hsep, hd, hdquarter, RM, RC, T, Q, ?_, ?_, ?_, ?_, hT, hTi, hTh, hTih,
    hTfilled, hQ, hQi, hQh, hQih, hQsource, hmatchM, hmatchC, hcore⟩
  · rw [hTs, hT0s]
    rfl
  · exact hTt.trans hT0t
  · intro p
    rw [hTv, hT0form]
  · intro p hp
    rw [hTinv, hT0inv p (hTt ▸ hp)]

end PoincareConjecture.M25.Topology3D
