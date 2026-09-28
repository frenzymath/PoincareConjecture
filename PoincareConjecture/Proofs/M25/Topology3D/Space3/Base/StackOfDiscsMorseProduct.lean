import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AmbientMorseChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapEnd











set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)



theorem exists_stackMorseProduct
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u q : UnitTwoSphere)
    (hq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q = 0)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hqe : q ∈ e.source) (heq : e q = 0)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ p ∈ e.source, ⟪(u : E3), psi (p, 0)⟫_ℝ =
      ⟪(u : E3), psi (q, 0)⟫_ℝ + kappa * ((e p).1 ^ 2 + (e p).2 ^ 2))
    (U : Set UnitTwoSphere) (hU : IsOpen U) (hqU : q ∈ U)
    (d : ℝ) (hd : 0 < d) :
    let L : E2 ≃L[ℝ] (ℝ × ℝ) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    let c := ⟪(u : E3), psi (q, 0)⟫_ℝ
    ∃ rho : ℝ, 0 < rho ∧ rho < d ∧
      ∃ A : OpenPartialHomeomorph (E2 × ℝ) E3,
        (0, c) ∈ A.source ∧ A (0, c) = psi (q, 0) ∧
        ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target ∧
        closedBall (0 : E2) (2 * rho) ×ˢ Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2)
          ⊆ A.source ∧
        (∀ p ∈ A.source,
          L p.1 ∈ e.target ∧ e.symm (L p.1) ∈ U ∧
          A p = (heightPlaneCoordinates u).symm
            ((heightPlaneCoordinates u (psi (e.symm (L p.1), 0))).1, p.2) ∧
          ⟪(u : E3), A p⟫_ℝ = p.2 ∧
          (A p ∈ range (fun r : UnitTwoSphere => psi (r, 0)) ↔
            p.2 = c + kappa * ‖p.1‖ ^ 2)) ∧
        ∀ x ∈ closedBall (0 : E2) (2 * rho),
          A (x, c + kappa * ‖x‖ ^ 2) = psi (e.symm (L x), 0) := by
  let L : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let c := ⟪(u : E3), psi (q, 0)⟫_ℝ
  have hnorm (x : E2) : ‖x‖ ^ 2 = (L x).1 ^ 2 + (L x).2 ^ 2 := by
    change ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  let eU := e.restrOpen U hU
  have heU : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ eU eU.source :=
    he.mono inter_subset_left
  have heiU : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ eU.symm eU.target :=
    hei.mono inter_subset_left
  have hformU : ∀ p ∈ eU.source, ⟪(u : E3), psi (p, 0)⟫_ℝ =
      c + kappa * (eU p).1 ^ 2 + kappa * (eU p).2 ^ 2 := by
    intro p hp
    rw [hform p hp.1]
    change c + kappa * ((e p).1 ^ 2 + (e p).2 ^ 2) = _
    dsimp [eU]
    ring
  obtain ⟨A0, h00, hA0, hA0i, hA0form⟩ :=
    exists_collar_ambient_morse_chart psi hpsi u q hq eU ⟨hqe, hqU⟩
      heq heU heiU kappa kappa hformU
  let V := L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  let A := V.toHomeomorph.transOpenPartialHomeomorph A0
  have h0A : (0, c) ∈ A.source := by
    change (L 0, c) ∈ A0.source
    simpa only [map_zero] using h00
  have hAs : ContDiffOn ℝ ∞ A A.source :=
    hA0.comp V.contDiff.contDiffOn (fun _ hp => hp)
  have hAi : ContDiffOn ℝ ∞ A.symm A.target :=
    V.symm.contDiff.comp_contDiffOn hA0i
  have hAF (p : E2 × ℝ) (hp : p ∈ A.source) :
      L p.1 ∈ e.target ∧ e.symm (L p.1) ∈ U ∧
      A p = (heightPlaneCoordinates u).symm
        ((heightPlaneCoordinates u (psi (e.symm (L p.1), 0))).1, p.2) ∧
      ⟪(u : E3), A p⟫_ℝ = p.2 ∧
      (A p ∈ range (fun r : UnitTwoSphere => psi (r, 0)) ↔
        p.2 = c + kappa * ‖p.1‖ ^ 2) := by
    have hf := hA0form (V p) hp
    refine ⟨hf.1.1, hf.1.2, hf.2.1, hf.2.2.1, ?_⟩
    change A0 (V p) ∈ range (fun r : UnitTwoSphere => psi (r, 0)) ↔ _
    rw [hf.2.2.2, hnorm]
    change (p.2 = c + kappa * (L p.1).1 ^ 2 + kappa * (L p.1).2 ^ 2) ↔ _
    ring_nf
  have hA0 : A (0, c) = psi (q, 0) := by
    rw [(hAF _ h0A).2.2.1, map_zero]
    have he0 : e.symm 0 = q := by rw [← heq, e.left_inv hqe]
    rw [he0]
    exact heightPlaneCoordinates_reconstruct u (psi (q, 0)) c rfl
  obtain ⟨eps, heps, hepsA⟩ := Metric.isOpen_iff.mp A.open_source (0, c) h0A
  obtain ⟨rho, hrho, hrbound⟩ := exists_between
    (show (0 : ℝ) < min d (min 1 (eps / 8)) from
      lt_min hd (lt_min zero_lt_one (div_pos heps (by norm_num))))
  have hrd : rho < d := hrbound.trans_le (min_le_left _ _)
  have hr1 : rho < 1 := hrbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hre : rho < eps / 8 :=
    hrbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hr2 : 2 * rho < eps := by linarith
  have hr4 : 4 * rho ^ 2 < eps := by nlinarith
  have hprod : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source := by
    intro p hp
    apply hepsA
    rw [mem_ball, Prod.dist_eq, dist_zero_right, Real.dist_eq]
    refine max_lt (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hp.1) hr2) ?_
    exact abs_lt.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  refine ⟨rho, hrho, hrd, A, h0A, hA0, hAs, hAi, hprod, hAF, ?_⟩
  intro x hx
  have hxnorm := mem_closedBall_zero_iff.mp hx
  have hxb : ‖x‖ ^ 2 ≤ 4 * rho ^ 2 := by nlinarith [norm_nonneg x]
  have hkap := abs_le.mp hkappa.le
  have ht : c + kappa * ‖x‖ ^ 2 ∈ Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) := by
    have hl := mul_le_mul_of_nonneg_right hkap.1 (sq_nonneg ‖x‖)
    have hu := mul_le_mul_of_nonneg_right hkap.2 (sq_nonneg ‖x‖)
    constructor <;> nlinarith
  have hp := hAF (x, c + kappa * ‖x‖ ^ 2) (hprod ⟨hx, ht⟩)
  rw [hp.2.2.1]
  apply heightPlaneCoordinates_reconstruct
  rw [hform _ (e.map_target hp.1), e.right_inv hp.1, hnorm]



theorem exists_stackMorseEndTube
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (A : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hA : ContDiffOn ℝ ∞ A A.source) (hAi : ContDiffOn ℝ ∞ A.symm A.target)
    (c kappa rho d : ℝ) (hkappa : |kappa| = 1) (hrho : 0 < rho) (hd : 0 < d)
    (hsource : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source)
    (hheight : ∀ p ∈ A.source, ⟪(u : E3), A p⟫_ℝ = p.2)
    (hgraph : ∀ p ∈ A.source,
      A p ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        p.2 = c + kappa * ‖p.1‖ ^ 2) :
    let s := c + kappa * rho ^ 2
    let H := fun y : E3 =>
      ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1)
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < d ∧ gamma < rho ^ 2 / 4 ∧
      ∃ T : OpenPartialHomeomorph P P,
        T.source = {p : P | 0 < kappa * (p.1 - c) ∧
          (Real.sqrt (kappa * (p.1 - c)) • p.2, p.1) ∈ A.source} ∧
        T.target = {p : P | (heightPlaneCoordinates u).symm (p.2, p.1) ∈ A.target ∧
          0 < kappa * (p.1 - c)} ∧
        (∀ p : P, T p = H (A (Real.sqrt (kappa * (p.1 - c)) • p.2, p.1))) ∧
        ContDiffOn ℝ ∞ T T.source ∧ ContDiffOn ℝ ∞ T.symm T.target ∧
        Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) (3 / 2) ⊆ T.source ∧
        (∀ z ∈ Icc (s - gamma) (s + gamma),
          rho ^ 2 / 2 < kappa * (z - c) ∧ kappa * (z - c) < 3 * rho ^ 2 / 2) ∧
        (∀ p ∈ T.source, (T p).1 = p.1) ∧
        (∀ p ∈ T.target,
          T.symm p = (p.1, (Real.sqrt (kappa * (p.1 - c)))⁻¹ •
            (A.symm ((heightPlaneCoordinates u).symm (p.2, p.1))).1)) ∧
        (∀ p ∈ T.source,
          (heightPlaneCoordinates u).symm ((T p).2, (T p).1) ∈
            range (fun q : UnitTwoSphere => psi (q, 0)) ↔ ‖p.2‖ = 1) ∧
        ∀ z ∈ Icc (s - gamma) (s + gamma),
          IsPlanarEmbedding (fun q : UnitCircle => (T (z, (q : E2))).2) ∧
          ∃ N : BallNeighborhoodChart E2 E2,
            N.chart.source = {x : E2 | (z, x) ∈ T.source} ∧
            N.chart.target = {y : E2 | (z, y) ∈ T.target} ∧
            (∀ x : E2, N.chart x = (T (z, x)).2) ∧
            (∀ y : E2, N.chart.symm y = (T.symm (z, y)).2) := by
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  have hkap2 : kappa ^ 2 = 1 := by nlinarith [sq_abs kappa]
  let s := c + kappa * rho ^ 2
  let H := (heightPlaneCoordinates u).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ)
  let root : ℝ → ℝ := fun z => Real.sqrt (kappa * (z - c))
  let Us : Set P := {p | 0 < kappa * (p.1 - c)}
  let Ut : Set (E2 × ℝ) := {p | 0 < kappa * (p.2 - c)}
  have hUs : IsOpen Us := isOpen_lt continuous_const
    (continuous_const.mul (continuous_fst.sub continuous_const))
  have hUt : IsOpen Ut := isOpen_lt continuous_const
    (continuous_const.mul (continuous_snd.sub continuous_const))
  have hrs : ContDiffOn ℝ ∞ (fun p : P => root p.1) Us :=
    (contDiff_const.mul (contDiff_fst.sub contDiff_const)).contDiffOn.sqrt
      (fun _ hp => ne_of_gt hp)
  have hrt : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => root p.2) Ut :=
    (contDiff_const.mul (contDiff_snd.sub contDiff_const)).contDiffOn.sqrt
      (fun _ hp => ne_of_gt hp)
  have hrpos (z : ℝ) (hz : 0 < kappa * (z - c)) : 0 < root z := Real.sqrt_pos.mpr hz
  have hBs : ContDiffOn ℝ ∞ (fun p : P => (root p.1 • p.2, p.1)) Us :=
    (hrs.smul contDiff_snd.contDiffOn).prodMk contDiff_fst.contDiffOn
  have hBi : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => (p.2, (root p.2)⁻¹ • p.1)) Ut :=
    contDiff_snd.contDiffOn.prodMk
      ((hrt.inv (fun p hp => (hrpos p.2 hp).ne')).smul contDiff_fst.contDiffOn)
  let B : OpenPartialHomeomorph P (E2 × ℝ) := {
    toFun := fun p => (root p.1 • p.2, p.1)
    invFun := fun p => (p.2, (root p.2)⁻¹ • p.1)
    source := Us
    target := Ut
    map_source' := fun _ hp => hp
    map_target' := fun _ hp => hp
    left_inv' := by
      intro p hp
      refine Prod.ext ?_ ?_
      · rfl
      · change (root p.1)⁻¹ • (root p.1 • p.2) = p.2
        rw [smul_smul, inv_mul_cancel₀ (hrpos p.1 hp).ne', one_smul]
    right_inv' := by
      intro p hp
      refine Prod.ext ?_ ?_
      · change root p.2 • ((root p.2)⁻¹ • p.1) = p.1
        rw [smul_smul, mul_inv_cancel₀ (hrpos p.2 hp).ne', one_smul]
      · rfl
    open_source := hUs
    open_target := hUt
    continuousOn_toFun := hBs.continuousOn
    continuousOn_invFun := hBi.continuousOn }
  let T := (B.trans A).transHomeomorph H.toHomeomorph
  have hiheight (y : E3) (hy : y ∈ A.target) : (A.symm y).2 = ⟪(u : E3), y⟫_ℝ := by
    have hh := hheight (A.symm y) (A.map_target hy)
    rw [A.right_inv hy] at hh
    exact hh.symm
  have hHheight (p : P) : ⟪(u : E3), H.symm p⟫_ℝ = p.1 := by
    rw [← heightPlaneCoordinates_snd]
    exact congrArg Prod.snd ((heightPlaneCoordinates u).apply_symm_apply (p.2, p.1))
  have htarget : T.target = {p : P | H.symm p ∈ A.target ∧ 0 < kappa * (p.1 - c)} := by
    ext p
    change (H.symm p ∈ A.target ∧ 0 < kappa * ((A.symm (H.symm p)).2 - c)) ↔ _
    constructor <;> intro hp
    · exact ⟨hp.1, by simpa only [hiheight _ hp.1, hHheight] using hp.2⟩
    · exact ⟨hp.1, by simpa only [hiheight _ hp.1, hHheight] using hp.2⟩
  have hTs : ContDiffOn ℝ ∞ T T.source :=
    H.contDiff.comp_contDiffOn (hA.comp (hBs.mono inter_subset_left) (fun _ hp => hp.2))
  have hTis : ContDiffOn ℝ ∞ T.symm T.target :=
    hBi.comp (hAi.comp H.symm.contDiff.contDiffOn (fun _ hp => hp.1)) (fun _ hp => hp.2)
  have hTh (p : P) (hp : p ∈ T.source) : (T p).1 = p.1 := by
    change (heightPlaneCoordinates u (A (root p.1 • p.2, p.1))).2 = p.1
    rw [heightPlaneCoordinates_snd]
    exact hheight _ hp.2
  have hTih (p : P) (hp : p ∈ T.target) : (T.symm p).1 = p.1 := by
    have hh := hTh (T.symm p) (T.map_target hp)
    rw [T.right_inv hp] at hh
    exact hh.symm
  obtain ⟨gamma, hgamma, hg⟩ := exists_between
    (lt_min hd (div_pos (sq_pos_of_pos hrho) (show (0 : ℝ) < 4 by norm_num)))
  have hgd : gamma < d := hg.trans_le (min_le_left _ _)
  have hgr : gamma < rho ^ 2 / 4 := hg.trans_le (min_le_right _ _)
  have hrad (z : ℝ) (hz : z ∈ Icc (s - gamma) (s + gamma)) :
      3 * rho ^ 2 / 4 < kappa * (z - c) ∧ kappa * (z - c) < 5 * rho ^ 2 / 4 := by
    have heq : kappa * (z - c) - rho ^ 2 = kappa * (z - s) := by
      dsimp [s]
      nlinarith only [hkap2]
    have hh : |kappa * (z - c) - rho ^ 2| ≤ gamma := by
      rw [heq, abs_mul, hkappa, one_mul]
      exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hb := abs_le.mp hh
    constructor <;> linarith only [hb.1, hb.2, hgr]
  have hprod : Icc (s - gamma) (s + gamma) ×ˢ
      closedBall (0 : E2) (3 / 2) ⊆ T.source := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    have hh := hrad z hz
    have hpos : 0 < kappa * (z - c) := lt_trans (by positivity) hh.1
    have hr := hrpos z hpos
    have hrsq : root z ^ 2 = kappa * (z - c) := Real.sq_sqrt hpos.le
    change 0 < kappa * (z - c) ∧ (root z • x, z) ∈ A.source
    refine ⟨hpos, hsource ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have hxnorm := mem_closedBall_zero_iff.mp hx
      have hx2 : ‖x‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg x]
      have hb : (root z * ‖x‖) ^ 2 ≤ (5 * rho ^ 2 / 4) * (9 / 4) := by
        rw [mul_pow, hrsq]
        exact mul_le_mul hh.2.le hx2 (sq_nonneg ‖x‖) (by positivity)
      nlinarith only [hb, hrho, sq_nonneg (root z * ‖x‖ - 2 * rho)]
    · have hab : |z - c| < 4 * rho ^ 2 := by
        calc
          |z - c| = |kappa * (z - c)| := by rw [abs_mul, hkappa, one_mul]
          _ = kappa * (z - c) := abs_of_pos hpos
          _ < 4 * rho ^ 2 := by nlinarith only [hh.2, sq_pos_of_pos hrho]
      constructor <;> linarith [(abs_lt.mp hab).1, (abs_lt.mp hab).2]
  have hradweak (z : ℝ) (hz : z ∈ Icc (s - gamma) (s + gamma)) :
      rho ^ 2 / 2 < kappa * (z - c) ∧ kappa * (z - c) < 3 * rho ^ 2 / 2 := by
    have hh := hrad z hz
    constructor <;> nlinarith only [hh.1, hh.2, sq_pos_of_pos hrho]
  refine ⟨gamma, hgamma, hgd, hgr, T, rfl, htarget, fun _ => rfl, hTs, hTis,
    hprod, hradweak, hTh, ?_, ?_, ?_⟩
  · intro p hp
    have hpat : H.symm p ∈ A.target := hp.1
    change ((A.symm (H.symm p)).2, (root (A.symm (H.symm p)).2)⁻¹ •
      (A.symm (H.symm p)).1) = _
    rw [hiheight (H.symm p) hpat, hHheight]
    rfl
  · intro p hp
    have hpA : (root p.1 • p.2, p.1) ∈ A.source := hp.2
    change H.symm (H (A (root p.1 • p.2, p.1))) ∈
      range (fun q : UnitTwoSphere => psi (q, 0)) ↔ _
    rw [H.symm_apply_apply, hgraph (root p.1 • p.2, p.1) hpA, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hrpos p.1 hp.1), mul_pow]
    have hrsq : root p.1 ^ 2 = kappa * (p.1 - c) := Real.sq_sqrt (le_of_lt hp.1)
    have hh : kappa * root p.1 ^ 2 = p.1 - c := by
      rw [hrsq, ← mul_assoc, show kappa * kappa = 1 by nlinarith only [hkap2], one_mul]
    rw [← mul_assoc, hh]
    have hne : p.1 - c ≠ 0 := by
      intro heq
      have hn := hp.1
      change 0 < kappa * (p.1 - c) at hn
      rw [heq, mul_zero] at hn
      exact (lt_irrefl 0) hn
    constructor
    · intro heq
      have hm : (p.1 - c) * (‖p.2‖ ^ 2 - 1) = 0 := by nlinarith only [heq]
      have hx := (mul_eq_zero.mp hm).resolve_left hne
      nlinarith only [hx, norm_nonneg p.2]
    · intro hx
      rw [hx]
      ring
  · intro z hz
    have hN : ∃ N : BallNeighborhoodChart E2 E2,
        N.chart.source = {x : E2 | (z, x) ∈ T.source} ∧
        N.chart.target = {y : E2 | (z, y) ∈ T.target} ∧
        (∀ x : E2, N.chart x = (T (z, x)).2) ∧
        (∀ y : E2, N.chart.symm y = (T.symm (z, y)).2) := by
      have hf : ContDiffOn ℝ ∞ (fun x : E2 => (T (z, x)).2)
          {x | (z, x) ∈ T.source} :=
        (hTs.comp (contDiff_prodMk_right z).contDiffOn (fun _ hx => hx)).snd
      have hi : ContDiffOn ℝ ∞ (fun y : E2 => (T.symm (z, y)).2)
          {y | (z, y) ∈ T.target} :=
        (hTis.comp (contDiff_prodMk_right z).contDiffOn (fun _ hy => hy)).snd
      have hforward (x : E2) (hx : (z, x) ∈ T.source) :
          (z, (T (z, x)).2) = T (z, x) := Prod.ext (hTh (z, x) hx).symm rfl
      have hinverse (y : E2) (hy : (z, y) ∈ T.target) :
          (z, (T.symm (z, y)).2) = T.symm (z, y) := Prod.ext (hTih (z, y) hy).symm rfl
      let e : OpenPartialHomeomorph E2 E2 := {
        toFun := fun x => (T (z, x)).2
        invFun := fun y => (T.symm (z, y)).2
        source := {x | (z, x) ∈ T.source}
        target := {y | (z, y) ∈ T.target}
        map_source' := by
          intro x hx
          change (z, (T (z, x)).2) ∈ T.target
          rw [hforward x hx]
          exact T.map_source hx
        map_target' := by
          intro y hy
          change (z, (T.symm (z, y)).2) ∈ T.source
          rw [hinverse y hy]
          exact T.map_target hy
        left_inv' := by
          intro x hx
          rw [hforward x hx, T.left_inv hx]
        right_inv' := by
          intro y hy
          rw [hinverse y hy, T.right_inv hy]
        open_source := T.open_source.preimage (continuous_const.prodMk continuous_id)
        open_target := T.open_target.preimage (continuous_const.prodMk continuous_id)
        continuousOn_toFun := hf.continuousOn
        continuousOn_invFun := hi.continuousOn }
      refine ⟨⟨e, ?_, hf, hi⟩, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
      intro x hx
      exact hprod ⟨hz, closedBall_subset_closedBall (by norm_num) hx⟩
    obtain ⟨N, hNs, hNt, hNf, hNi⟩ := hN
    have he : (N.chart : E2 → E2) = fun x => (T (z, x)).2 := funext hNf
    refine ⟨?_, N, hNs, hNt, hNf, hNi⟩
    have hsm : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞
        (fun q : UnitCircle => (T (z, (q : E2))).2) := by
      intro q
      have hq := N.closedBall_subset_source (sphere_subset_closedBall q.property)
      have hh := N.smooth.contDiffAt (N.chart.open_source.mem_nhds hq)
      rw [he] at hh
      exact hh.contMDiffAt.comp q contMDiff_coe_sphere.contMDiffAt
    refine ⟨hsm, ?_, ?_⟩
    · intro p q hpq
      apply Subtype.ext
      apply N.chart.injOn
        (N.closedBall_subset_source (sphere_subset_closedBall p.property))
        (N.closedBall_subset_source (sphere_subset_closedBall q.property))
      rw [he]
      exact hpq
    · intro q
      let i : UnitCircle → E2 := fun p => (p : E2)
      have hi : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ i := contMDiff_coe_sphere
      have hdi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) i q) := by
        intro v w hvw
        exact injective_mvfderiv_subtypeVal_sphere q
          (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (q : E2)) hvw)
      have hq := N.closedBall_subset_source (sphere_subset_closedBall q.property)
      obtain ⟨D, hD⟩ := exists_smoothChart_derivative N.chart N.smooth N.smooth_symm hq
      have hcomp : (fun q : UnitCircle => (T (z, (q : E2))).2) = N.chart ∘ i := by
        funext p
        exact (congrFun he (p : E2)).symm
      rw [hcomp, mfderiv_comp q hD.differentiableAt.mdifferentiableAt
        (hi.mdifferentiable (by simp) q), mfderiv_eq_fderiv, hD.fderiv]
      exact D.injective.comp hdi

end PoincareConjecture.M25.Topology3D
