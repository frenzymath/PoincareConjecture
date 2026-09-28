import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_common_radial_fields
    (e delta : ℝ) (he : 0 < e) (heSmall : e < 1 / 512)
    (hdelta : 0 < delta)
    (b : Fin 2 → ℝ × E2 → E2)
    (hb : ∀ j : Fin 2, ContDiff ℝ ∞ (b j))
    (P : Set E2) (hP : IsCompact P)
    (E : Fin 2 → ℝ → Set E2)
    (hExterior : ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
      E j t ⊆ P ∩ {x : E2 | 1 ≤ ‖x‖})
    (hAnnulus : ∀ (j : Fin 2) (t : ℝ) (x : E2),
      |t| < 2 * delta → x ∈ E j t → ‖x‖ ≤ 1 + 3 * e →
        b 0 (t, x) = b j (t, x) ∧ ⟪x, b 0 (t, x)⟫_ℝ = 0) :
    ∃ (C : ℝ × E2 → E2) (W : Fin 2 → ℝ × E2 → E2)
      (K : Set E2),
      ContDiff ℝ ∞ C ∧ HasCompactSupport C ∧
      (∀ j : Fin 2, ContDiff ℝ ∞ (W j) ∧ HasCompactSupport (W j)) ∧
      IsCompact K ∧
      tsupport C ⊆ Icc (-3 * delta) (3 * delta) ×ˢ K ∧
      (∀ j : Fin 2,
        tsupport (W j) ⊆ Icc (-3 * delta) (3 * delta) ×ˢ K) ∧
      (∀ (t : ℝ) (x : E2), ⟪x, C (t, x)⟫_ℝ = 0) ∧
      (∀ (j : Fin 2) (t : ℝ) (x : E2), ‖x‖ ≤ 1 + 2 * e →
        W j (t, x) = C (t, x)) ∧
      ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
        EqOn (fun x : E2 => W j (t, x)) (fun x => b j (t, x)) (E j t) := by
  have hsmall : 0 < 1 - e := by linarith only [heSmall]
  have hsqSmall : (1 - e) ^ 2 < 1 := by
    nlinarith only [he, mul_pos he hsmall]
  have hsq34 : (1 + 3 * e) ^ 2 < (1 + 4 * e) ^ 2 := by
    nlinarith only [he, sq_nonneg e]
  have hsq23 : (1 + 2 * e) ^ 2 < (1 + 3 * e) ^ 2 := by
    nlinarith only [he, sq_nonneg e]
  obtain ⟨theta, htheta, _hctheta, hstheta, hnearTheta, _hthetaBounds⟩ :=
    exists_compact_smooth_cutoff
      (K := Icc (1 : ℝ) ((1 + 3 * e) ^ 2))
      (U := Ioo ((1 - e) ^ 2) ((1 + 4 * e) ^ 2))
      isCompact_Icc isOpen_Ioo (fun _ hx =>
        ⟨hsqSmall.trans_le hx.1, hx.2.trans_lt hsq34⟩)
  obtain ⟨ell, hell, _hcell, hsell, hnearEll, _hellBounds⟩ :=
    exists_compact_smooth_cutoff
      (K := Icc (0 : ℝ) ((1 + 2 * e) ^ 2))
      (U := Ioo (-1 : ℝ) ((1 + 3 * e) ^ 2))
      isCompact_Icc isOpen_Ioo (fun _ hx =>
        ⟨by linarith only [hx.1], hx.2.trans_lt hsq23⟩)
  obtain ⟨tau, htau, _hctau, hstau, hnearTau, _htauBounds⟩ :=
    exists_compact_smooth_cutoff
      (K := Icc (-2 * delta) (2 * delta))
      (U := Ioo (-3 * delta) (3 * delta))
      isCompact_Icc isOpen_Ioo (fun _ hx =>
        ⟨by linarith only [hx.1, hdelta], by linarith only [hx.2, hdelta]⟩)
  obtain ⟨beta, hbeta, hcbeta, _hsbeta, hnearBeta, _hbetaBounds⟩ :=
    exists_compact_smooth_cutoff (U := univ) hP isOpen_univ (subset_univ _)
  have hthetaOne (q : ℝ) (hq : q ∈ Icc (1 : ℝ) ((1 + 3 * e) ^ 2)) :
      theta q = 1 := (eventually_nhdsSet_iff_forall.mp hnearTheta q hq).self_of_nhds
  have hellOne (q : ℝ) (hq : q ∈ Icc (0 : ℝ) ((1 + 2 * e) ^ 2)) :
      ell q = 1 := (eventually_nhdsSet_iff_forall.mp hnearEll q hq).self_of_nhds
  have htauOne (t : ℝ) (ht : |t| < 2 * delta) : tau t = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnearTau t
      ⟨by linarith only [(abs_lt.mp ht).1], (abs_lt.mp ht).2.le⟩).self_of_nhds
  have hbetaOne (x : E2) (hx : x ∈ P) : beta x = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnearBeta x hx).self_of_nhds
  let Rad : ℝ × E2 → E2 := fun p =>
    b 0 p - (⟪p.2, b 0 p⟫_ℝ / ‖p.2‖ ^ 2) • p.2
  let C : ℝ × E2 → E2 := fun p => (tau p.1 * theta (‖p.2‖ ^ 2)) • Rad p
  let W : Fin 2 → ℝ × E2 → E2 := fun j p =>
    ell (‖p.2‖ ^ 2) • C p +
      (tau p.1 * (1 - ell (‖p.2‖ ^ 2)) * beta p.2) • b j p
  let K : Set E2 := closedBall (0 : E2) (1 + 4 * e) ∪ tsupport beta
  have hK : IsCompact K := (isCompact_closedBall (0 : E2) _).union hcbeta.isCompact
  have hq : ContDiff ℝ ∞ (fun p : ℝ × E2 => ‖p.2‖ ^ 2) :=
    contDiff_snd.norm_sq ℝ
  have hC : ContDiff ℝ ∞ C := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : ‖p.2‖ ^ 2 ∈ tsupport theta
    · have hq0 : ‖p.2‖ ^ 2 ≠ 0 :=
        ((sq_pos_of_pos hsmall).trans (hstheta hp).1).ne'
      have hRad : ContDiffAt ℝ ∞ Rad p :=
        (hb 0).contDiffAt.sub
          (((contDiffAt_snd.inner ℝ (hb 0).contDiffAt).div hq.contDiffAt hq0).smul
            contDiffAt_snd)
      exact ((htau.comp contDiff_fst).mul (htheta.comp hq)).contDiffAt.smul hRad
    · have hn : ∀ᶠ v : ℝ × E2 in 𝓝 p, ‖v.2‖ ^ 2 ∉ tsupport theta :=
        ((isClosed_tsupport theta).isOpen_compl.preimage hq.continuous).mem_nhds hp
      apply (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : ℝ × E2 => (0 : E2)) p).congr_of_eventuallyEq
      filter_upwards [hn] with v hv
      simp only [C, image_eq_zero_of_notMem_tsupport hv, mul_zero, zero_smul]
  have hW (j : Fin 2) : ContDiff ℝ ∞ (W j) :=
    ((hell.comp hq).smul hC).add
      (((htau.comp contDiff_fst).mul (contDiff_const.sub (hell.comp hq))).mul
        (hbeta.comp contDiff_snd) |>.smul (hb j))
  have hzero (p : ℝ × E2) (hp : p ∉ Icc (-3 * delta) (3 * delta) ×ˢ K) :
      C p = 0 ∧ ∀ j : Fin 2, W j p = 0 := by
    by_cases ht : p.1 ∈ Icc (-3 * delta) (3 * delta)
    · have hx : p.2 ∉ K := fun hx => hp ⟨ht, hx⟩
      have hxb : p.2 ∉ closedBall (0 : E2) (1 + 4 * e) := fun hh => hx (Or.inl hh)
      have hr : 1 + 4 * e < ‖p.2‖ := lt_of_not_ge (fun hh => hxb
        (mem_closedBall_zero_iff.mpr hh))
      have hthetaZ : theta (‖p.2‖ ^ 2) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hh
        have hn := (hstheta hh).2
        have hs := mul_pos (by linarith only [hr] : 0 < ‖p.2‖ - (1 + 4 * e))
          (by linarith only [he, norm_nonneg p.2] : 0 < ‖p.2‖ + (1 + 4 * e))
        nlinarith only [hn, hs]
      have hbetaZ : beta p.2 = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hx (Or.inr hh))
      have hCZ : C p = 0 := by simp only [C, hthetaZ, mul_zero, zero_smul]
      exact ⟨hCZ, fun j => by simp only [W, hCZ, hbetaZ, smul_zero, mul_zero,
        zero_smul, add_zero]⟩
    · have htauZ : tau p.1 = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => ht ⟨(hstau hh).1.le, (hstau hh).2.le⟩)
      have hCZ : C p = 0 := by simp only [C, htauZ, zero_mul, zero_smul]
      exact ⟨hCZ, fun j => by simp only [W, hCZ, htauZ, smul_zero, zero_mul,
        zero_smul, add_zero]⟩
  have hcompact : IsCompact (Icc (-3 * delta) (3 * delta) ×ˢ K) :=
    isCompact_Icc.prod hK
  have hCs : tsupport C ⊆ Icc (-3 * delta) (3 * delta) ×ˢ K :=
    closure_minimal (fun p hp => by by_contra hn; exact hp (hzero p hn).1)
      hcompact.isClosed
  have hWs (j : Fin 2) : tsupport (W j) ⊆ Icc (-3 * delta) (3 * delta) ×ˢ K :=
    closure_minimal (fun p hp => by by_contra hn; exact hp ((hzero p hn).2 j))
      hcompact.isClosed
  refine ⟨C, W, K, hC, hcompact.of_isClosed_subset (isClosed_tsupport C) hCs,
    fun j => ⟨hW j, hcompact.of_isClosed_subset (isClosed_tsupport (W j)) (hWs j)⟩,
    hK, hCs, hWs, ?_, ?_, ?_⟩
  · intro t x
    by_cases hx : x = 0
    · simp only [hx, inner_zero_left]
    · have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
      simp only [C, Rad, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]
      rw [div_mul_cancel₀ _ hn, sub_self, mul_zero]
  · intro j t x hx
    have hs : ‖x‖ ^ 2 ≤ (1 + 2 * e) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg x) hx 2
    simp only [W, hellOne _ ⟨sq_nonneg _, hs⟩, one_smul, sub_self,
      mul_zero, zero_mul, zero_smul, add_zero]
  · intro j t ht x hx
    obtain ⟨hxP, hxnorm⟩ := hExterior j t ht hx
    change 1 ≤ ‖x‖ at hxnorm
    have ht1 := htauOne t ht
    have hb1 := hbetaOne x hxP
    by_cases hEll : ell (‖x‖ ^ 2) = 0
    · simp only [W, hEll, ht1, hb1, zero_smul, sub_zero, mul_one, one_smul, zero_add]
    · have hqbound := (hsell (subset_tsupport ell hEll)).2
      have hnorm : ‖x‖ ≤ 1 + 3 * e := by
        nlinarith only [hqbound, norm_nonneg x, he]
      obtain ⟨hmatch, hrad⟩ := hAnnulus j t x ht hx hnorm
      have hq1 : 1 ≤ ‖x‖ ^ 2 := by
        simpa only [one_pow] using
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hxnorm 2
      have htheta1 := hthetaOne (‖x‖ ^ 2) ⟨hq1, hqbound.le⟩
      have hCeq : C (t, x) = b j (t, x) := by
        simp only [C, Rad, ht1, htheta1, one_mul, one_smul, hrad, zero_div,
          zero_smul, sub_zero]
        exact hmatch
      simp only [W, hCeq, ht1, hb1, one_mul, mul_one]
      rw [← add_smul]
      simp only [add_sub_cancel, one_smul]

end PoincareConjecture.M25.Topology3D
