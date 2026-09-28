import PoincareConjecture.Proofs.M25.AppA_1_Necks.EuclideanMetric
import PoincareConjecture.Proofs.M25.AppA_1_Necks.RicciControl
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Overlap_A11

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

private theorem exists_sign_axis_error {H t τ : ℝ}
    (hτ : 0 < τ) (hcap : τ ≤ 1 / 200) (hH : 0 ≤ H) (hHτ : H ≤ 6 * τ)
    (hmetric : |2 * H + t ^ 2 - 1| ≤ 3 * τ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 2 * (2 * H + (t - σ) ^ 2) ≤ 27 * τ := by
  have ht : |t ^ 2 - 1| ≤ 15 * τ := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hmetric).1, (abs_le.mp hmetric).2]
  have hroot (z : ℝ) (hz : 0 ≤ z) : |z - 1| ≤ |z ^ 2 - 1| := by
    have heq : |z ^ 2 - 1| = |z - 1| * (z + 1) := by
      rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring,
        abs_mul, abs_of_nonneg (by linarith : 0 ≤ z + 1)]
    rw [heq]
    nlinarith [abs_nonneg (z - 1)]
  have hsign : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ |t - σ| ≤ 15 * τ := by
    by_cases hpos : 0 ≤ t
    · exact ⟨1, Or.inl rfl, (hroot t hpos).trans ht⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have h := (hroot (-t) (by linarith)).trans (by simpa only [neg_sq] using ht)
      simpa only [show -t - 1 = -(t - -1) by ring, abs_neg] using h
  obtain ⟨σ, hσ, herror⟩ := hsign
  have hsq : (t - σ) ^ 2 ≤ (15 * τ) ^ 2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (t - σ)) herror
  refine ⟨σ, hσ, ?_⟩
  nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hcap)]

theorem exists_normalized_axis_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ (q q' : UnitTwoSphere) {s s' : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      s' ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
      N.coordinate_map (q, s) = N'.coordinate_map (q', s') →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        g.tangentNorm (N.coordinate_map (q, s))
          ((show TangentSpace (𝓡 3) (N.coordinate_map (q, s)) from
              N'.normalizedEuclideanFrame q' s' (m25_roundCylinderEuclideanBasis 2)) -
            σ • N.normalizedEuclideanFrame q s (m25_roundCylinderEuclideanBasis 2)) < α := by
  let τ : ℝ := min (1 / 200) (α ^ 2 / 100)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτcap : τ ≤ 1 / 200 := min_le_left _ _
  have hτα : τ ≤ α ^ 2 / 100 := min_le_right _ _
  obtain ⟨εR, hεR, _, hRicci⟩ := exists_normalized_ricci_quadratic_control.{u} hτ
  obtain ⟨εS, hεS, _, hscale⟩ := exists_intersecting_scale_control.{u} (by norm_num : (0 : ℝ) < 1)
  refine ⟨min τ (min εR εS), lt_min hτ (lt_min hεR hεS),
    (min_le_left _ _).trans hτcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' q q' s s' hs hs' hx
  have hNτ := hN.trans (min_le_left _ _)
  have hN'τ := hN'.trans (min_le_left _ _)
  have hNR := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN'R := hN'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNS := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hN'S := hN'.trans ((min_le_right _ _).trans (min_le_right _ _))
  let x := N.coordinate_map (q, s)
  let e := m25_roundCylinderEuclideanBasis 2
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let G := fun v : EuclideanSpace ℝ (Fin 3) => roundCylinderEuclideanModelCoefficients 0 v v
  let A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    N.normalizedEuclideanFrame q s
  let A' : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    N'.normalizedEuclideanFrame q' s'
  let F : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0
  let F' : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) (N'.euclideanParametrization q' s') 0
  let R : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
    RicciFlow.Splitting.ricciBilinear N.connection x
  have hTe : T e = (0, 1) := m25_lineModelEquiv_symm_roundCylinderEuclideanBasis 2
  have hRapply (v w : EuclideanSpace ℝ (Fin 3)) : R v w = N.connection.ricci x v w :=
    RicciFlow.Splitting.ricciBilinear_apply _ _ v w
  have hGe : G e = 1 := by
    dsimp only [G]
    rw [roundCylinderEuclideanModelCoefficients_zero]
    change 2 * ‖(T e).1‖ ^ 2 + (T e).2 ^ 2 = 1
    rw [hTe]
    norm_num
  have hne : ‖e‖ ^ 2 = 1 := by
    rw [RiemannianMetric.lineModelEquiv_norm_sq]
    change ‖(T e).1‖ ^ 2 + (T e).2 ^ 2 = 1
    rw [hTe]
    norm_num
  have hmetric (v : EuclideanSpace ℝ (Fin 3)) :
      |g.inner x (A v) (A v) - G v| ≤ N.epsilon * G v := by
    change |g.inner (N.coordinate_map (q, s))
      (N.normalizedEuclideanFrame q s v) (N.normalizedEuclideanFrame q s v) - G v| ≤ _
    rw [N.normalizedEuclideanFrame_inner q hs]
    exact N.normalizedEuclideanCoefficients_quadratic_error q hs v
  have hmetric' (v : EuclideanSpace ℝ (Fin 3)) :
      |g.inner x (A' v) (A' v) - G v| ≤ N'.epsilon * G v := by
    change |g.inner (N.coordinate_map (q, s)) (A' v) (A' v) - G v| ≤ _
    rw [hx]
    change |g.inner (N'.coordinate_map (q', s'))
      (N'.normalizedEuclideanFrame q' s' v) (N'.normalizedEuclideanFrame q' s' v) - G v| ≤ _
    rw [N'.normalizedEuclideanFrame_inner q' hs']
    exact N'.normalizedEuclideanCoefficients_quadratic_error q' hs' v
  obtain ⟨v, hv⟩ := (N.normalizedEuclideanFrame_bijective q hs).2 (A' e)
  change A v = A' e at hv
  have hGnonneg : 0 ≤ G v :=
    (sq_nonneg ‖v‖).trans (norm_sq_le_roundCylinderEuclideanModelCoefficients v)
  have hm := hmetric v
  rw [hv] at hm
  have hm' := hmetric' e
  rw [hGe, mul_one] at hm'
  have hG : G v ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hNτ hGnonneg
    have hmulcap := mul_le_mul_of_nonneg_right hτcap hGnonneg
    nlinarith [(abs_le.mp hm).1, (abs_le.mp hm').2]
  have hnv : ‖v‖ ^ 2 ≤ 2 := (norm_sq_le_roundCylinderEuclideanModelCoefficients v).trans hG
  have hGerror : |G v - 1| ≤ 3 * τ := by
    have hmul := mul_le_mul hNτ hG hGnonneg hτ.le
    have htriangle := abs_sub_le (G v) (g.inner x (A' e) (A' e)) 1
    rw [abs_sub_comm (G v) (g.inner x (A' e) (A' e))] at htriangle
    linarith
  let r := N.scale / N'.scale
  have hrpos : 0 < r := div_pos N.scale_pos N'.scale_pos
  have hr : r < 2 := by
    have hi : (N'.carrier ∩ N.carrier).Nonempty := by
      refine ⟨x, ?_, ?_⟩
      · change N.coordinate_map (q, s) ∈ N'.carrier
        rw [hx]
        exact N'.coordinate_map_mem ⟨mem_univ _, hs'⟩
      · exact N.coordinate_map_mem ⟨mem_univ _, hs⟩
    have h := (hscale N' N hN'S hNS hi).2
    change |r - 1| < 1 at h
    linarith [(abs_lt.mp h).2]
  have hFv : F v = r • F' e := by
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => N.scale • w) hv
    change N.scale • (N.scale⁻¹ • F v) = N.scale • (N'.scale⁻¹ • F' e) at h
    simpa only [smul_smul, mul_inv_cancel₀ N.scale_pos.ne', one_smul, r,
      div_eq_mul_inv] using h
  have hRu : |R (F v) (F v) - ‖(T v).1‖ ^ 2| ≤ τ * ‖v‖ ^ 2 := by
    rw [hRapply]
    exact hRicci N hNR q hs v
  have hR'e : |R (F' e) (F' e)| ≤ τ := by
    have h := hRicci N' hN'R q' hs' e
    change |N'.connection.ricci (N'.coordinate_map (q', s')) (F' e) (F' e) -
      ‖(T e).1‖ ^ 2| ≤ τ * ‖e‖ ^ 2 at h
    rw [hTe, hne] at h
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] at h
    rw [← hx] at h
    have hR : N'.connection.ricci x (F' e) (F' e) = N.connection.ricci x (F' e) (F' e) := by
      unfold LeviCivitaData.ricci
      simp_rw [N'.connection.horizon_curvatureTensor_eq N.connection x]
    exact (congrArg abs ((hRapply _ _).trans hR.symm)).trans_le h
  have hRv : |R (F v) (F v)| ≤ 4 * τ := by
    have heq : R (F v) (F v) = r ^ 2 * R (F' e) (F' e) := by
      rw [hFv]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [heq, abs_mul, abs_of_nonneg (sq_nonneg r)]
    exact (mul_le_mul_of_nonneg_left hR'e (sq_nonneg r)).trans
      (mul_le_mul_of_nonneg_right (by nlinarith : r ^ 2 ≤ 4) hτ.le)
  have hH : ‖(T v).1‖ ^ 2 ≤ 6 * τ := by
    have hmul := mul_le_mul_of_nonneg_left hnv hτ.le
    linarith [(abs_le.mp hRu).1, (abs_le.mp hRv).2]
  have hGform : G v = 2 * ‖(T v).1‖ ^ 2 + (T v).2 ^ 2 :=
    roundCylinderEuclideanModelCoefficients_zero v
  rw [hGform] at hGerror
  obtain ⟨σ, hσ, herror⟩ := exists_sign_axis_error hτ hτcap
    (sq_nonneg ‖(T v).1‖) hH hGerror
  refine ⟨σ, hσ, ?_⟩
  have hGsub : G (v - σ • e) = 2 * ‖(T v).1‖ ^ 2 + ((T v).2 - σ) ^ 2 := by
    dsimp only [G]
    rw [roundCylinderEuclideanModelCoefficients_zero]
    change 2 * ‖(T (v - σ • e)).1‖ ^ 2 + (T (v - σ • e)).2 ^ 2 = _
    simp [map_sub, map_smul, hTe]
  have hAsub : A (v - σ • e) = A' e - σ • A e := by rw [map_sub, map_smul, hv]
  have hbound : g.inner x (A' e - σ • A e) (A' e - σ • A e) ≤ 27 * τ := by
    have hm := (abs_le.mp (hmetric (v - σ • e))).2
    rw [hAsub] at hm
    have hnonneg : 0 ≤ G (v - σ • e) := by rw [hGsub]; positivity
    have hmul := mul_le_mul_of_nonneg_right (show N.epsilon ≤ 1 by linarith) hnonneg
    rw [← hGsub] at herror
    linarith
  change Real.sqrt (g.inner x (A' e - σ • A e) (A' e - σ • A e)) < α
  exact (Real.sqrt_lt' hα).mpr (hbound.trans_lt (by nlinarith [sq_pos_of_pos hα]))

end PoincareConjecture.EpsilonNeck
