import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderParameterJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.M34

open DifferenceEnergy



theorem partialFlow_endCylinderParameterDifference_zero
    {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
    (e : StandardCylindricalEnd g0.metric) (j : ℕ) (q : UnitTwoSphere)
    {p : RoundCylinderCoordinates} (hp : 2 < p.2) :
    endCylinderParameterDifference e F.flow j 0 q p = 0 := by
  have hp0 : 0 < p.2 := lt_trans (by norm_num : (0 : ℝ) < 2) hp
  have hj : 0 < p.2 + (j : ℝ) := add_pos_of_pos_of_nonneg hp0 (Nat.cast_nonneg j)
  have hz : endCylinderDifferenceCoefficients e F.flow j 0
      (endSphereCylinderMap e q p) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    have he := endAxialTranslation_metric e (j : ℝ)
      (z := ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) hp0 hj v w
    simp only [endCylinderDifferenceCoefficients, Pi.sub_apply, sub_apply,
      endCylinderCoefficients_apply, F.initial_metric, sub_zero, one_mul, zero_mul,
      add_zero, zero_apply]
    change _ - _ = 0
    exact sub_eq_zero.mpr he.symm
  rw [endCylinderParameterDifference_eq_pullback e F.flow j 0 q hp, hz]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rfl



theorem partialFlow_lifetime_le_one_of_end_jets
    (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    (e : StandardCylindricalEnd g0.metric)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (p₀ : endReferenceRegion e) :
    F.lifetime ≤ 1 := by
  by_contra! hlong
  obtain ⟨K, hK, hKb⟩ := F.curvature_locally_bounded 1 zero_le_one hlong
  let ell : ℝ := Real.exp (-6 * K)
  have hell : 0 < ell := Real.exp_pos _
  have hell1 : ell ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  let T : ℝ := 1 - ell / 2
  have hT0 : 0 ≤ T := by dsimp [T]; linarith
  have hT1 : T < 1 := by dsimp [T]; linarith
  have hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1 :=
    ⟨⟨hT0, hT1.trans hlong⟩, ⟨hT0, hT1⟩⟩
  obtain ⟨N, hN⟩ := partialFlow_endCylinderParameterDifference_iteratedFDeriv_tendsto
    P E0 F e qH qA qS p₀ hT 0 (half_pos hell)
  let q : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  let v : RoundCylinderCoordinates := (EuclideanSpace.single 0 1, 0)
  have hv : ‖v‖ = 1 := by simp [v, Prod.norm_def]
  have hmodel (t : ℝ) : evolvingRoundCylinderModelCoefficients t (0, 4) v v =
      2 * (1 - t) := by
    norm_num [evolvingRoundCylinderModelCoefficients_apply, v]
  let f := endAxialTranslation e (N + 1 : ℕ) ∘ endSphereCylinderMap e q
  have hinit : g0.metric.parametrizedCoefficients f (0, 4) v v = 2 := by
    have hi := congrArg (fun B => B v v)
      (partialFlow_endCylinderParameterDifference_zero F e (N + 1) q
        (p := (0, 4)) (by norm_num))
    simp only [endCylinderParameterDifference, sub_apply, F.initial_metric,
      zero_apply, hmodel] at hi
    change g0.metric.parametrizedCoefficients f (0, 4) v v - 2 * (1 - 0) = 0 at hi
    linarith
  have hcomparison := (partialFlow_exp_bounds F P hT.1 hK
    (fun s hs x => (le_abs_self _).trans (hKb s ⟨hs.1, hs.2.trans hT1.le⟩ x))
    (f (0, 4)) (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f (0, 4) v)).1
  change Real.exp (-6 * K * T) * g0.metric.parametrizedCoefficients f (0, 4) v v ≤
    (F.flow.metric T).parametrizedCoefficients f (0, 4) v v at hcomparison
  rw [hinit] at hcomparison
  have hexp : ell ≤ Real.exp (-6 * K * T) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hlower : 2 * ell ≤ (F.flow.metric T).parametrizedCoefficients f (0, 4) v v := by
    nlinarith
  have herror := hN N le_rfl T ⟨hT0, le_rfl⟩ q 4 (by norm_num)
  simp only [norm_iteratedFDeriv_zero] at herror
  have heval := (endCylinderParameterDifference e F.flow (N + 1) T q (0, 4)).le_opNorm₂ v v
  rw [hv, mul_one, mul_one] at heval
  have hsmall := heval.trans_lt herror
  simp only [endCylinderParameterDifference, sub_apply, hmodel, Real.norm_eq_abs] at hsmall
  have habs := (le_abs_self _).trans_lt hsmall
  change (F.flow.metric T).parametrizedCoefficients f (0, 4) v v - 2 * (1 - T) < ell / 2
    at habs
  dsimp [T] at habs
  linarith

end PoincareConjecture.M34
