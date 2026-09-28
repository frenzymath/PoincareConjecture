import PoincareConjecture.Proofs.M47.BlowupControlsCapStrictAnalytics

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem exists_cap_height_analytic_tolerance {g : RiemannianMetric 3 M}
    (N : CapCertificate g) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ bR bG bE : ℝ,
      bR < N.cap_constant ∧ bG < N.cap_constant ∧ bE < N.cap_constant ∧
      ∀ h : ℝ, 0 < h → ∀ R G E : M → ℝ,
        (∀ x ∈ N.carrier,
          ‖(h ^ 2 * R x, h ^ 3 * G x, h ^ 4 * E x) -
            (N.connection.scalarCurvature x, scalarGradientNorm g N.connection x,
              N.connection.laplacian N.connection.scalarCurvature x +
                2 * N.connection.ricciNormSq x)‖ ≤ nu) →
        (∀ x ∈ N.carrier, 0 < R x) ∧
        (∀ x ∈ N.carrier, ∀ y ∈ N.carrier, R y ≤ bR * R x) ∧
        (∀ x ∈ N.carrier, G x ≤ bG * R x ^ (3 / 2 : ℝ)) ∧
        ∀ x ∈ N.carrier, |E x| ≤ bE * R x ^ 2 := by
  obtain ⟨nu, hnu, bR, bG, bE, hbR, hbG, hbE, hbound⟩ :=
    exists_cap_strict_analytic_tolerance N
  refine ⟨nu, hnu, bR, bG, bE, hbR, hbG, hbE, ?_⟩
  intro h hh R G E hclose
  have hcomponents (x : M) (hx : x ∈ N.carrier) :
      |h ^ 2 * R x - N.connection.scalarCurvature x| ≤ nu ∧
      |h ^ 3 * G x - scalarGradientNorm g N.connection x| ≤ nu ∧
      |h ^ 4 * E x - (N.connection.laplacian N.connection.scalarCurvature x +
        2 * N.connection.ricciNormSq x)| ≤ nu := by
    have htuple := hclose x hx
    refine ⟨?_, ?_, ?_⟩
    · exact (norm_fst_le _).trans htuple
    · exact (norm_fst_le _).trans ((norm_snd_le _).trans htuple)
    · exact (norm_snd_le _).trans ((norm_snd_le _).trans htuple)
  obtain ⟨hpositive, hratio, hgradient, hevolution⟩ :=
    hbound (fun x => h ^ 2 * R x) (fun x => h ^ 3 * G x)
      (fun x => h ^ 4 * E x) hcomponents
  have hR (x : M) (hx : x ∈ N.carrier) : 0 < R x := by
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) (le_of_not_gt hnot)
    exact (hpositive x hx).not_ge hnonpos
  refine ⟨hR, ?_, ?_, ?_⟩
  · intro x hx y hy
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hh)).mp
    simpa only [mul_left_comm] using hratio x hx y hy
  · intro x hx
    have hpower : (h ^ 2) ^ (3 / 2 : ℝ) = h ^ 3 := by
      rw [← Real.rpow_natCast h 2, ← Real.rpow_mul hh.le]
      norm_num
    have hestimate := hgradient x hx
    rw [Real.mul_rpow (sq_nonneg h) (hR x hx).le, hpower] at hestimate
    apply (mul_le_mul_iff_right₀ (pow_pos hh 3)).mp
    simpa only [mul_left_comm] using hestimate
  · intro x hx
    have hestimate := hevolution x hx
    rw [abs_mul, abs_of_pos (pow_pos hh 4), mul_pow] at hestimate
    have hpower : (h ^ 2) ^ 2 = h ^ 4 := by ring
    rw [hpower] at hestimate
    apply (mul_le_mul_iff_right₀ (pow_pos hh 4)).mp
    simpa only [mul_left_comm] using hestimate

end PoincareConjecture.M47
