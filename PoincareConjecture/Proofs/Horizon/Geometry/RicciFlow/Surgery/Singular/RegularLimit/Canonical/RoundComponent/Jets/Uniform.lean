import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Initial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Ellipticity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Parametrization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.PairwiseMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.TimeControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Scale



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit.RoundComparison

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}




theorem exists_uniform_round_coordinate_terminal_bound
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold)
    (x : H.regularRegion P04) (hpos : 0 < (H.terminalConnection P04).scalarCurvature x)
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (m : ℕ) (hm : m ≤ ⌊H.epsilon⁻¹⌋₊) :
    ∃ s B : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 ≤ B ∧
      ∀ t ∈ Ico s T,
        ∀ N : SingularRoundComponent ((H.terminalFlow P04).metric t) H.epsilon,
          x ∈ N.carrier → N.carrier ⊆ A → ∀ y : N.model.carrier,
          ∃ (U : Set E) (f : E → N.model.carrier), IsOpen U ∧ (0 : E) ∈ U ∧ f 0 = y ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
            (∀ z ∈ U, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible) ∧
            (∀ z ∈ U, ∀ v w : E, sphereReferenceMetric.inner z v w =
              N.model_metric.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z v)
                (mfderiv (𝓡 3) (𝓡 3) f z w)) ∧
            ∀ j ≤ m,
              ‖iteratedFDeriv ℝ j ((H.terminalMetric P04).pullbackCoefficients (N.forward ∘ f)) 0 -
                iteratedFDeriv ℝ j (((H.terminalFlow P04).metric t).pullbackCoefficients
                  (N.forward ∘ f)) 0‖ ≤ B * (T - t) := by
  classical
  let l := (H.terminalConnection P04).scalarCurvature x / 14
  let u := 2 * (H.terminalConnection P04).scalarCurvature x / 5
  have hl : 0 < l := by dsimp [l]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  obtain ⟨a, haT, hscale⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (H.eventually_roundComponent_scale_bounds P04 hepsilon x hpos)
  obtain ⟨sK, hsK, hsKT, hcurv⟩ := H.exists_terminalFlow_curvature_derivative_tail_on_compact P04 hA
  choose K hK hcurv using hcurv
  obtain ⟨sG, hsG, hsGT, hmetric⟩ := H.exists_terminalFlow_pairwise_metric_tail P04 hA
  obtain ⟨Z, hZ, hinit⟩ := exists_round_initial_coordinate_jet_bound.{u} m
  obtain ⟨B, hB, htime⟩ := SpacetimeBounds.exists_terminal_spatialJet_time_constant
    3 m K (fun _ => Z / l) (fun j => (hK j).le)
    (a := 1 / (8 * u)) (b := 8 / l) (by positivity) (by positivity)
  obtain ⟨s, hs, hsT⟩ := exists_between
    (max_lt hsKT (max_lt hsGT (max_lt haT (by linarith : T - 1 < T))))
  have hssK : sK < s := (le_max_left _ _).trans_lt hs
  have hssG : sG < s := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  have hsa : a < s := (le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  have hsone : T - 1 < s := (le_max_right _ _).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  refine ⟨s, B, hsK.trans hssK, hsT, hB, ?_⟩
  intro t ht N hxN hNA y
  have hsc : l < N.scale ∧ N.scale < u := hscale ⟨hsa.trans_le ht.1, ht.2⟩ N hxN
  obtain ⟨U, f, hU, hzero, hfzero, hf, hinv, hmodel, hjets⟩ := hinit N
    (le_trans hepsilon (le_trans roundComparisonThreshold_le (by norm_num))) hm y
  refine ⟨U, f, hU, hzero, hfzero, hf, hinv, hmodel, ?_⟩
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (N.forward ∘ f) U :=
    N.forward_smooth.comp_contMDiffOn hf
  have heinv : ∀ z ∈ U, (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) z).IsInvertible :=
    fun z hz => N.forward_comp_mfderiv_invertible hU hf hinv hz
  have hyA : N.forward (f 0) ∈ A := hNA (N.forward_image ▸ mem_range_self (f 0))
  have htG : t ∈ Ico sG T := ⟨hssG.le.trans ht.1, ht.2⟩
  have hell : ∀ r ∈ Ico t T, ∀ v : E,
      (1 / (8 * u)) * ‖v‖ ^ 2 ≤ ((H.terminalFlow P04).metric r).pullbackCoefficients
        (N.forward ∘ f) 0 v v ∧
      ((H.terminalFlow P04).metric r).pullbackCoefficients (N.forward ∘ f) 0 v v ≤
        (8 / l) * ‖v‖ ^ 2 := by
    intro r hr v
    have hrG : r ∈ Ico sG T := ⟨htG.1.trans hr.1, hr.2⟩
    have hquad := N.normalizedMetric_centered_ellipticity hepsilon (hmodel 0 hzero) v
    rw [N.normalizedMetric_pullbackCoefficients_eq hU hf hzero] at hquad
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ N.scale *
      ((H.terminalFlow P04).metric t).pullbackCoefficients (N.forward ∘ f) 0 v v ∧
      N.scale * ((H.terminalFlow P04).metric t).pullbackCoefficients (N.forward ∘ f) 0 v v ≤
        2 * ‖v‖ ^ 2 at hquad
    have hnonneg : 0 ≤ ((H.terminalFlow P04).metric t).pullbackCoefficients
        (N.forward ∘ f) 0 v v := by nlinarith [N.scale_pos, sq_nonneg ‖v‖]
    have hupper := mul_le_mul_of_nonneg_right hsc.2.le hnonneg
    have hlower := mul_le_mul_of_nonneg_right hsc.1.le hnonneg
    have htr := hmetric t htG r hrG _ hyA (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) 0 v)
    have hrt := hmetric r hrG t htG _ hyA (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ f) 0 v)
    change ((H.terminalFlow P04).metric t).pullbackCoefficients (N.forward ∘ f) 0 v v ≤
      4 * ((H.terminalFlow P04).metric r).pullbackCoefficients (N.forward ∘ f) 0 v v at htr
    change ((H.terminalFlow P04).metric r).pullbackCoefficients (N.forward ∘ f) 0 v v ≤
      4 * ((H.terminalFlow P04).metric t).pullbackCoefficients (N.forward ∘ f) 0 v v at hrt
    constructor
    · rw [one_div_mul_eq_div]
      apply (div_le_iff₀ (by positivity : 0 < 8 * u)).mpr
      nlinarith [mul_le_mul_of_nonneg_left htr hu.le]
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hl).mpr
      nlinarith [mul_le_mul_of_nonneg_left hrt hl.le]
  have hinit' : ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (((H.terminalFlow P04).metric t).pullbackCoefficients
        (N.forward ∘ f)) 0‖ ≤ Z / l := by
    intro j hj
    have h := hjets j hj
    rw [N.normalizedMetric_pullback_jet_eq hU hf hzero j, norm_smul,
      Real.norm_eq_abs, abs_of_pos N.scale_pos] at h
    apply (le_div_iff₀ hl).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsc.1.le
      (norm_nonneg (iteratedFDeriv ℝ j (((H.terminalFlow P04).metric t).pullbackCoefficients
        (N.forward ∘ f)) 0))]
  intro j hj
  have h := htime (H.terminalFlow P04) hU he heinv
    ((hsK.trans hssK).trans_le ht.1) ht.2 (by linarith [ht.1]) hzero hell
    (fun k _ r hr => hcurv k r ⟨hssK.le.trans (ht.1.trans hr.1), hr.2⟩ _ hyA)
    hinit' j hj
  rwa [H.terminalFlow_metric_at_terminal P04] at h

end PoincareConjecture.SingularTimeAssumptions
