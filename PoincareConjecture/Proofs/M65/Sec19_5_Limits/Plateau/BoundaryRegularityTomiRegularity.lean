import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTomiBootstrap

set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

open EuclideanTranslationNative

private theorem small_pairing_neighborhood {N : ℕ}
    (u : Fin N → ScalarL2 2) (f v : Fin N → LoopPlane → ℝ)
    (E : LoopPlane → ℝ) (hE0 : ∀ z, 0 ≤ E z)
    {U : Set LoopPlane} (hU : IsOpen U) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U → |f j z| ≤ C * E z)
    (hv : ∀ j, ContinuousOn (v j) U)
    (huv : ∀ j, (u j : LoopPlane → ℝ) =ᵐ[volume.restrict U] v j)
    {p : LoopPlane} (hp : p ∈ U) :
    ∃ r > 0, ball p r ⊆ U ∧ ∃ V ≥ 0,
      (∀ x ∈ ball p r, ∀ j, |v j x| ≤ V) ∧
      ∀ x ∈ ball p r, ∀ᵐ z ∂volume, z ∈ ball p r →
        |∑ j : Fin N, f j z * (u j z - v j x)| ≤ E z / 2 := by
  classical
  let ε := 1 / (4 * ((N : ℝ) + 1) * (C + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hfactor : (N : ℝ) * (C * (2 * ε)) ≤ 1 / 2 := by
    have hden : 0 < 4 * ((N : ℝ) + 1) * (C + 1) := by positivity
    have heq : 4 * ((N : ℝ) + 1) * (C + 1) * ε = 1 := mul_one_div_cancel hden.ne'
    have hh : (N : ℝ) * C ≤ ((N : ℝ) + 1) * (C + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hprod := mul_le_mul_of_nonneg_right hh hε.le
    nlinarith only [hprod, heq]
  have hclose (j : Fin N) : ∀ᶠ x in 𝓝 p, |v j x - v j p| < ε := by
    have hc := (hv j p hp).continuousAt (hU.mem_nhds hp)
    simpa only [mem_ball, dist_eq_norm, Real.norm_eq_abs] using
      hc.tendsto.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))
  have hmem : ∀ᶠ x in 𝓝 p, x ∈ U := hU.mem_nhds hp
  have hnear : ∀ᶠ x in 𝓝 p, x ∈ U ∧ ∀ j, |v j x - v j p| < ε :=
    hmem.and (eventually_all.mpr hclose)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hnear
  let V := ε + ∑ j : Fin N, |v j p|
  have hV : 0 ≤ V := add_nonneg hε.le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨r, hr, fun x hx => (hrU hx).1, V, hV, ?_, ?_⟩
  · intro x hx j
    calc
      |v j x| = |(v j x - v j p) + v j p| := by rw [sub_add_cancel]
      _ ≤ |v j x - v j p| + |v j p| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (v j x - v j p) (v j p)
      _ ≤ V := add_le_add ((hrU hx).2 j).le
        (Finset.single_le_sum (fun k _ => abs_nonneg (v k p)) (Finset.mem_univ j))
  intro x hx
  have hAE (j : Fin N) : ∀ᵐ z ∂volume, z ∈ U → u j z = v j z :=
    (ae_restrict_iff' hU.measurableSet).mp (huv j)
  filter_upwards [ae_all_iff.mpr hgrowth, ae_all_iff.mpr hAE] with z hfz huz hz
  have hzU := (hrU hz).1
  have hdiff (j : Fin N) : |u j z - v j x| ≤ 2 * ε := by
    rw [huz j hzU]
    calc
      |v j z - v j x| ≤ |v j z - v j p| + |v j p - v j x| := abs_sub_le _ _ _
      _ ≤ ε + ε := add_le_add ((hrU hz).2 j).le
        (by rw [abs_sub_comm]; exact ((hrU hx).2 j).le)
      _ = 2 * ε := by ring
  calc
    |∑ j : Fin N, f j z * (u j z - v j x)| ≤
        ∑ j : Fin N, |f j z * (u j z - v j x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin N, |f j z| * |u j z - v j x| := by simp_rw [abs_mul]
    _ ≤ ∑ _j : Fin N, (C * E z) * (2 * ε) := Finset.sum_le_sum fun j _ =>
      mul_le_mul (hfz j hzU) (hdiff j) (abs_nonneg _) (mul_nonneg hC (hE0 z))
    _ = ((N : ℝ) * (C * (2 * ε))) * E z := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ (1 / 2) * E z := mul_le_mul_of_nonneg_right hfactor (hE0 z)
    _ = E z / 2 := by ring

set_option maxHeartbeats 1400000 in

theorem quadratic_holder_contDiffAt {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f v : Fin N → LoopPlane → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {S : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) S)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {C B H β Λ R : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hΛ : 0 ≤ Λ) (hR : 0 < R)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2))
    (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hv : ∀ j, ContinuousOn (v j) U)
    (huv : ∀ j, (u j : LoopPlane → ℝ) =ᵐ[volume.restrict U] v j)
    (hholder : ∀ x ∈ U, ∀ z ∈ U, ∀ j, |v j z - v j x| ≤ H * ‖z - x‖ ^ β)
    {p : LoopPlane} (hp : p ∈ U)
    (hdecay : ∀ x ∈ ball p R, ∀ r : ℝ, 0 < r → r ≤ R →
      (∫ z in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) ≤
        Λ * r ^ (2 * β)) :
    ∀ j, ContDiffAt ℝ 1 (v j) p := by
  let E := fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2
  have hE : Integrable E := integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun i _ => (Lp.memLp (d j i)).integrable_sq
  have hE0 (z : LoopPlane) : 0 ≤ E z := by dsimp only [E]; positivity
  obtain ⟨r0, hr0, hsub, V, hV, hvalue, hsmall⟩ :=
    small_pairing_neighborhood u f v E hE0 hU hC hgrowth hv huv hp
  have hp0 : p ∈ ball p r0 := mem_ball_self hr0
  have hgrowth0 (j : Fin N) : ∀ᵐ z ∂volume, z ∈ ball p r0 → |f j z| ≤ C * E z := by
    filter_upwards [hgrowth j] with z hz hzU
    exact hz (hsub hzU)
  have heq0 (j : Fin N) (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ ball p r0) :
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z) := heq j φ hc (hs.trans hsub)
  have hholder0 (x : LoopPlane) (hx : x ∈ ball p r0) (j : Fin N) :
      ∀ᵐ z ∂volume, z ∈ ball p r0 → |u j z - v j x| ≤ H * ‖z - x‖ ^ β := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp (huv j)] with z hz hzU
    rw [hz (hsub hzU)]
    exact hholder x (hsub hx) z (hsub hzU) j
  have hinitial := initial_energy_weight E hE hE0 p hR hβ hΛ hdecay
  obtain ⟨a, ha, henergy⟩ := energy_weight_above_one u d f v hf isOpen_ball hfs hweak heq0
    hC hV hH hβ hgrowth0 hbound hvalue hsmall hholder0 hp0 hinitial
  obtain ⟨r, hr, _hrsub, hregular⟩ := C1_of_energy_weight u d f v hf isOpen_ball hfs hweak heq0
    hC ha hgrowth0 (fun j => (hv j).mono hsub)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (huv j)) hp0 henergy
  intro j
  exact (hregular j p (mem_ball_self hr)).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))

end PoincareConjecture.M65Boundary
