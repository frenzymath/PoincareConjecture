import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_InitialDerivative
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalStripModel















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_exists_uniform_normal_expansion_subinterval_radius
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ b : ℝ, 0 < b → b ≤ R → ∀ (N : IntrinsicAnnulus) (radius : ℝ), radius ≠ 0 →
        N.GaussianCurvatureBound K →
        ∀ (u : ℝ × ℝ → AnnulusCoordinates) (S I : Set ℝ),
          IsOpen S → IsOpen I → Icc (0 : ℝ) b ⊆ I →
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I) →
          (∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I) →
          (∀ s ∈ S, u (s, 0) = intrinsicAnnulusBoundary radius s) →
          ∀ normal : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ normal →
            (∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s)
              (normal s) (normal s) = 1) →
            (∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s) (normal s)
              (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) s) = 0) →
            (∀ s ∈ S, curveVelocity (n := 2) (fun t => u (s, t)) 0 = normal s) →
            ∀ a ∈ S,
              intrinsicGeodesicCurvature N.metric N.connection radius a ≤ alpha →
              (∀ t ∈ Ioo (0 : ℝ) b, u (a, t) ∈ standardAnnulusDomain) →
              ∃ W : ℝ → AnnulusCoordinates, ∀ t ∈ Icc (0 : ℝ) b,
                ContDiffAt ℝ ∞ W t ∧
                N.metric.inner (u (a, t)) (W t) (W t) = 1 ∧
                N.metric.inner (u (a, t)) (W t)
                  (curveVelocity (n := 2) (fun r => u (a, r)) t) = 0 ∧
                (1 - delta) * intrinsicBoundarySpeed N.metric radius a ≤
                  N.metric.inner (u (a, t))
                    (curveVelocity (n := 2) (fun s => u (s, t)) a) (W t) ∧
                (1 - delta) * intrinsicBoundarySpeed N.metric radius a ≤
                  N.metric.tangentNorm (u (a, t))
                    (curveVelocity (n := 2) (fun s => u (s, t)) a) := by
  let kappa := Real.sqrt (max K 1)
  have hmax : 0 < max K 1 := zero_lt_one.trans_le (le_max_right K 1)
  have hkappa : 0 < kappa := Real.sqrt_pos.mpr hmax
  have hKkappa : K ≤ kappa ^ 2 := by
    rw [Real.sq_sqrt hmax.le]
    exact le_max_left K 1
  obtain ⟨R, hR, hRsmall, hcomp⟩ :=
    m64Intrinsic_exists_uniform_normal_jacobi_subinterval_radius hdelta hdelta1 hkappa halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro b hb hbR N radius hradius hK u S I hS hI hsub hu hgeo hboundary
    normal hnormal hunit horth hvelocity a ha hturn hmap
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hq : DifferentiableAt ℝ (fun t => u (a, t)) 0 := by
    exact ((hu.contDiffOn.contDiffAt ((hS.prod hI).mem_nhds ⟨ha, hsub hz⟩)).comp 0
      (show ContDiffAt ℝ ∞ (fun t : ℝ => (a, t)) 0 from by fun_prop)).differentiableAt
        (by simp)
  have hnormal0 : HasDerivAt (fun t => u (a, t)) (normal a) 0 := by
    have h := hq.hasDerivAt
    rw [← m64Intrinsic_curveVelocity_eq_deriv, hvelocity a ha] at h
    exact h
  obtain ⟨W, j, v, hWzero, hjzero, hdata⟩ :=
    m64Intrinsic_exists_normal_scalar_jacobi N hradius hS hI hu hgeo hboundary ha hb hsub
      (hunit a) (horth a) hnormal0
  have hinitial : -alpha ≤ v 0 := by
    obtain ⟨_, _, _, _, _, hv, _, _, _⟩ := hdata 0 hz
    have hD := m64Intrinsic_normal_variation_initial_covDeriv N hS hI (hsub hz) hu
      hboundary hnormal hvelocity ha
    rw [hD, hWzero] at hv
    dsimp only at hv
    erw [hboundary a ha] at hv
    have hlow := m64Intrinsic_boundary_normal_turning_lower N hradius hnormal hunit horth a
    rw [hv]
    simpa only [div_eq_mul_inv, mul_comm] using (neg_le_neg hturn).trans hlow
  have hj : ∀ t ∈ Icc (0 : ℝ) b, 1 - delta ≤ j t := by
    apply hcomp b hb hbR j v (fun t => -(N.connection.scalarCurvature (u (a, t)) / 2) * j t)
      (fun t => N.connection.scalarCurvature (u (a, t)) / 2)
    · intro t ht
      exact (hdata t ht).2.2.2.2.2.2.1
    · intro t ht
      exact (hdata t ht).2.2.2.2.2.2.2.1.continuousAt.continuousWithinAt
    · intro t ht
      exact (hdata t ⟨ht.1.le, ht.2.le⟩).2.2.2.2.2.2.2.1
    · exact hjzero
    · exact hinitial
    · intro t _
      ring
    · intro t ht
      exact (hK (u (a, t)) (hmap t ht)).trans hKkappa
  refine ⟨W, ?_⟩
  intro t ht
  obtain ⟨hW, hWunit, hWorth, _, hjeq, _, _, _, _⟩ := hdata t ht
  have hs := m64Intrinsic_boundarySpeed_pos N hradius a
  have hlower : (1 - delta) * intrinsicBoundarySpeed N.metric radius a ≤
      N.metric.inner (u (a, t))
        (curveVelocity (n := 2) (fun s => u (s, t)) a) (W t) := by
    exact (le_div_iff₀ hs).mp (by simpa only [hjeq] using hj t ht)
  have hWnorm : N.metric.tangentNorm (u (a, t)) (W t) = 1 := by
    change Real.sqrt (N.metric.inner (u (a, t)) (W t) (W t)) = 1
    rw [hWunit, Real.sqrt_one]
  have hpair := m64Intrinsic_abs_metric_pairing_le N.metric (u (a, t))
    (curveVelocity (n := 2) (fun s => u (s, t)) a) (W t)
  rw [hWnorm, mul_one] at hpair
  exact ⟨hW, hWunit, hWorth, hlower, hlower.trans ((le_abs_self _).trans hpair)⟩



theorem m64Intrinsic_exists_uniform_normal_expansion_radius
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ (N : IntrinsicAnnulus) (radius : ℝ), radius ≠ 0 →
        N.GaussianCurvatureBound K →
        ∀ (u : ℝ × ℝ → AnnulusCoordinates) (S I : Set ℝ),
          IsOpen S → IsOpen I → Icc (0 : ℝ) R ⊆ I →
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I) →
          (∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I) →
          (∀ s ∈ S, u (s, 0) = intrinsicAnnulusBoundary radius s) →
          ∀ normal : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ normal →
            (∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s)
              (normal s) (normal s) = 1) →
            (∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s) (normal s)
              (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) s) = 0) →
            (∀ s ∈ S, curveVelocity (n := 2) (fun t => u (s, t)) 0 = normal s) →
            ∀ a ∈ S,
              intrinsicGeodesicCurvature N.metric N.connection radius a ≤ alpha →
              (∀ t ∈ Ioo (0 : ℝ) R, u (a, t) ∈ standardAnnulusDomain) →
              ∃ W : ℝ → AnnulusCoordinates, ∀ t ∈ Icc (0 : ℝ) R,
                ContDiffAt ℝ ∞ W t ∧
                N.metric.inner (u (a, t)) (W t) (W t) = 1 ∧
                N.metric.inner (u (a, t)) (W t)
                  (curveVelocity (n := 2) (fun r => u (a, r)) t) = 0 ∧
                (1 - delta) * intrinsicBoundarySpeed N.metric radius a ≤
                  N.metric.inner (u (a, t))
                    (curveVelocity (n := 2) (fun s => u (s, t)) a) (W t) ∧
                (1 - delta) * intrinsicBoundarySpeed N.metric radius a ≤
                  N.metric.tangentNorm (u (a, t))
                    (curveVelocity (n := 2) (fun s => u (s, t)) a) := by
  obtain ⟨R, hR, hRsmall, h⟩ :=
    m64Intrinsic_exists_uniform_normal_expansion_subinterval_radius K hdelta hdelta1 halpha
  exact ⟨R, hR, hRsmall, h R hR le_rfl⟩

end PoincareConjecture
