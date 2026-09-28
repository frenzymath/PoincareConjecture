import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUBochnerEnergy
import PoincareConjecture.Proofs.M60.Mathlib.SUHeinzScaling
import PoincareConjecture.Proofs.M01.ConnectionExistence










set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]




theorem m60HarmonicSphere_energy_regularity (g : RiemannianMetric n M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ (f : UnitTwoSphere → M),
      ContMDiff (𝓡 2) (𝓡 n) ∞ f → M60SphereChartHarmonic g f →
      ∀ (z : LoopPlane) (R : ℝ), 0 < R →
        (∫ x in Metric.closedBall z R, m60SphereEnergyDensity g f x) ≤ ε →
        R ^ 2 * m60SphereEnergyDensity g f z ≤
          C * (∫ x in Metric.closedBall z R, m60SphereEnergyDensity g f x) := by
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  obtain ⟨K, hK, hbochner⟩ := m60HarmonicSphere_uniform_bochner D
  obtain ⟨A, hA, hheinz⟩ := M60.exists_heinz_estimate_all_radii
  have hAK : 0 < A * K := mul_pos hA hK
  refine ⟨1 / (A * K), by positivity, A, hA, fun f hf hharm z R hR hsmall => ?_⟩
  let a := m60SphereEnergyDensity g f
  let v : LoopPlane → ℝ := fun x => a (z + x)
  have ha : ContDiff ℝ ∞ a := m60SphereEnergyDensity_contDiff g f hf
  have hv : ContDiff ℝ ∞ v := ha.comp (contDiff_const.add contDiff_id)
  have hv0 (x : LoopPlane) : 0 ≤ v x :=
    m60EnergyDensity_nonneg g (f ∘ m60SphereParameter) (z + x)
  have hlap (x : LoopPlane) (_hx : x ∈ Metric.ball 0 R) :
      -K * (v x) ^ 2 ≤ M60.suPlaneLaplacian v x := by
    rw [M60.suPlaneLaplacian_add_left]
    exact hbochner f hf hharm (z + x)
  have hint : (∫ x in Metric.closedBall 0 R, v x) =
      ∫ x in Metric.closedBall z R, a x := M60.suSetIntegral_closedBall_add_left a z R
  have hsm : A * K * (∫ x in Metric.closedBall 0 R, v x) ≤ 1 := by
    rw [hint]
    have h := (le_div_iff₀ hAK).mp hsmall
    nlinarith only [h]
  have h := hheinz K R hK.le hR v hv hv0 hlap hsm
  rw [hint] at h
  simpa only [v, add_zero] using h




theorem m60HarmonicSphere_small_energy_density_zero (g : RiemannianMetric n M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (f : UnitTwoSphere → M),
      ContMDiff (𝓡 2) (𝓡 n) ∞ f → M60SphereChartHarmonic g f →
      m60SphereEnergy g f ≤ ε → ∀ z : LoopPlane, m60SphereEnergyDensity g f z = 0 := by
  obtain ⟨ε, hε, C, hC, hest⟩ := m60HarmonicSphere_energy_regularity g
  refine ⟨ε, hε, fun f hf hharm hsmall z => ?_⟩
  let a := m60SphereEnergyDensity g f
  let E := m60SphereEnergy g f
  have hE : 0 ≤ E := m60SphereEnergy_nonneg g f
  have ha0 (x : LoopPlane) : 0 ≤ a x := m60EnergyDensity_nonneg g (f ∘ m60SphereParameter) x
  have hai : Integrable a volume := m60SphereEnergyDensity_integrable g f (hf.of_le (by simp))
  have hmass (R : ℝ) : (∫ x in Metric.closedBall z R, a x) ≤ E :=
    setIntegral_le_integral hai (Eventually.of_forall ha0)
  have hbound (R : ℝ) (hR : 0 < R) : R ^ 2 * a z ≤ C * E := by
    have h := hest f hf hharm z R hR ((hmass R).trans hsmall)
    exact h.trans (mul_le_mul_of_nonneg_left (hmass R) hC.le)
  by_contra hz
  have haz : 0 < a z := lt_of_le_of_ne (ha0 z) (Ne.symm hz)
  let R : ℝ := (C * E + 1) / a z + 1
  have hR1 : 1 < R := by
    have hdiv : 0 < (C * E + 1) / a z := by positivity
    dsimp only [R]
    linarith only [hdiv]
  have hRu : R * a z = C * E + 1 + a z := by
    dsimp only [R]
    field_simp [haz.ne']
  have hR2 : R ≤ R ^ 2 := by nlinarith only [hR1]
  have hm := mul_le_mul_of_nonneg_right hR2 haz.le
  have hb := hbound R (lt_trans zero_lt_one hR1)
  linarith only [hm, hb, hRu, haz]

end PoincareConjecture
