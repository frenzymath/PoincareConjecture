import PoincareConjecture.Proofs.M47.LimitNoncollapseVolume
import PoincareConjecture.Proofs.M47.LimitNoncollapseContractedTest









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47





theorem limitNoncollapse_of_finite_slabs
    (P : M47Predecessors.{u})
    {S : GeneralizedBlowupSequence.{u}} {H : ENNReal}
    (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))
    {kappa r0 : ℝ} (hkappa : 0 < kappa) (hr0 : 0 < r0)
    (hslabs : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < H →
      ∀ A : ℝ, 0 < A →
      ∀ᶠ k : ℕ in atTop,
        Nonempty (M30FiniteHorizonSlab S k A T kappa r0)) :
    BlowupLimitNoncollapsed G.limit kappa := by
  classical
  dsimp only [BlowupLimitNoncollapsed]
  let : TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
  let : MeasurableSpace G.limit.carrier.carrier := G.limit.carrier.measurableSpace
  let : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
    G.limit.carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  intro t ht p r hr htime hcurv
  apply limitNoncollapse_exact_density_of_theta_bounds
  intro theta htheta
  let rho := theta ^ 2 * r
  let sigma := theta * r
  let lambda := (1 + theta) / 2
  have hrho : 0 < rho := mul_pos (sq_pos_of_pos htheta.1) hr
  have hsigma : 0 < sigma := mul_pos htheta.1 hr
  have hlambda : 0 < lambda := by dsimp [lambda]; linarith [htheta.1]
  have hlambda_lt : lambda < 1 := by dsimp [lambda]; linarith [htheta.2]
  have htheta_lambda : theta < lambda := by dsimp [lambda]; linarith [htheta.2]
  have hrho_sigma : rho < sigma := by
    apply mul_lt_mul_of_pos_right _ hr
    nlinarith [htheta.1, htheta.2]
  have hsigma_r : sigma < r := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right htheta.2 hr
  have hgap : rho / lambda < sigma := by
    apply (div_lt_iff₀ hlambda).mpr
    have h := mul_lt_mul_of_pos_right htheta_lambda hsigma
    dsimp [rho, sigma] at h ⊢
    nlinarith
  obtain ⟨R, hbuffer, hRsigma⟩ := exists_between hgap
  have hR : 0 < R := (div_pos hrho hlambda).trans hbuffer
  have hvolume := limitNoncollapse_contracted_test_volume G P t ht p hr hrho
    (hrho_sigma.trans hsigma_r) hR (hRsigma.trans hsigma_r) hlambda hlambda_lt
    hbuffer hr0 hslabs htime hcurv
  have hpower : theta ^ 3 ≤ lambda ^ 3 :=
    pow_le_pow_left₀ htheta.1.le htheta_lambda.le 3
  have hdensity : kappa * theta ^ 9 * r ^ 3 ≤ kappa * lambda ^ 3 * rho ^ 3 := by
    calc
      _ = kappa * theta ^ 3 * rho ^ 3 := by dsimp [rho]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hkappa.le) (pow_nonneg hrho.le 3)
  exact (ENNReal.ofReal_le_ofReal hdensity).trans hvolume

end PoincareConjecture.M47
