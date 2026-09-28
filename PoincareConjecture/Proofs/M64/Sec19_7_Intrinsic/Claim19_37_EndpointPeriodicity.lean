import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalPeriodicity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MeasurableContact











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture




theorem m64Intrinsic_normal_endpoint_periodic
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hnormalPeriod : Function.Periodic normal rampPeriod)
    (hend : ∀ z : ℝ × ℝ, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ gamma : ℝ → AnnulusCoordinates,
        G.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
        gamma 0 = intrinsicAnnulusBoundary 1 z.1 ∧
        HasDerivAt gamma (z.2 • normal z.1) 0 ∧ gamma 1 = u z)
    (t : ℝ) : Function.Periodic (fun a => u (a, t)) rampPeriod := by
  intro a
  obtain ⟨epsilon, hepsilon, gamma, hgamma, hinit, hderiv, hlast⟩ := hend (a, t)
  obtain ⟨eta, heta, sigma, hsigma, hstart, hvelocity, hendpoint⟩ :=
    hend (a + rampPeriod, t)
  have hgamma' : G.IsGeodesicOn gamma (Icc (0 : ℝ) 1) := by
    intro s hs
    exact hgamma s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsigma' : G.IsGeodesicOn sigma (Icc (0 : ℝ) 1) := by
    intro s hs
    exact hsigma s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hzero : sigma 0 = gamma 0 := by
    rw [hstart, hinit, m64Intrinsic_boundary_periodic 1 a]
  have hvel : deriv (fun s => extChartAt (𝓡 2) (sigma 0) (sigma s)) 0 =
      deriv (fun s => extChartAt (𝓡 2) (sigma 0) (gamma s)) 0 := by
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
    rw [hvelocity.deriv, hderiv.deriv, hnormalPeriod a]
  have heq := hsigma'.eq_nhds_on_of_initial_data hgamma'
    (convex_Icc (0 : ℝ) 1).isPreconnected (t₀ := 0) (by simp)
    (sigma 0) (by simp) hzero hvel
  simpa only [hendpoint, hlast] using (heq 1 (by simp)).self_of_nhds




theorem m64Intrinsic_first_contact_height_periodic
    {u : ℝ × ℝ → AnnulusCoordinates} {height : ℝ → ℝ} {R : ℝ}
    (hu : ∀ t, Function.Periodic (fun a => u (a, t)) rampPeriod)
    (hheight : ∀ a : ℝ, 0 < height a ∧ height a ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) (height a), 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2) ∧
      (height a = R ∨ ‖u (a, height a)‖ = 1 ∨ ‖u (a, height a)‖ = 2)) :
    Function.Periodic height rampPeriod := by
  intro a
  apply m64Intrinsic_first_annulus_contact_unique (q := fun t => u (a, t))
    (hheight (a + rampPeriod)).1 (hheight a).1
    (hheight (a + rampPeriod)).2.1 (hheight a).2.1
  · intro t ht
    simpa only [hu t a] using (hheight (a + rampPeriod)).2.2.1 t ht
  · exact (hheight a).2.2.1
  · simpa only [hu (height (a + rampPeriod)) a] using
      (hheight (a + rampPeriod)).2.2.2
  · exact (hheight a).2.2.2

end PoincareConjecture
