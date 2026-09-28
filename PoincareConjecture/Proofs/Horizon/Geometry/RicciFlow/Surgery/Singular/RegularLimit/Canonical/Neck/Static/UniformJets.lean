import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.InitialJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TailTimeControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.PairwiseMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.MetricSurgery

theorem normalizedNeckMetric_centered_jet
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (j : ℕ) :
    iteratedFDeriv ℝ j ((normalizedNeckMetric N).pullbackCoefficients
        (centeredNeckLift N z.1 z.2)) 0 =
      N.connection.scalarCurvature N.center •
        iteratedFDeriv ℝ j (g.pullbackCoefficients (centeredNeckLift N z.1 z.2)) 0 := by
  have heq : (normalizedNeckMetric N).pullbackCoefficients (centeredNeckLift N z.1 z.2) =
      fun y => N.connection.scalarCurvature N.center •
        g.pullbackCoefficients (centeredNeckLift N z.1 z.2) y := by
    funext y
    ext v w
    rfl
  rw [heq]
  apply iteratedFDeriv_const_smul_apply'
  exact (g.contDiffAt_pullbackCoefficients
    (centeredNeckLift_contMDiffAt N z.1 z.2 (zero_mem_centeredNeckDomain N hz))).of_le
    (by exact_mod_cast le_top)

end PoincareConjecture.MetricSurgery

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_uniform_static_neck_coordinate_tail_bound
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    {ε l u : ℝ} (hε : ε ≤ 1 / 200) (hl : 0 < l) (hu : 0 < u)
    (m : ℕ) (hm : m ≤ ⌊ε⁻¹⌋₊) :
    ∃ s B : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 ≤ B ∧
      ∀ t ∈ Ico s T, ∀ N : EpsilonNeck ((H.terminalFlow P04).metric t),
        N.epsilon = ε → N.carrier ⊆ A →
        l ≤ N.connection.scalarCurvature N.center →
        N.connection.scalarCurvature N.center ≤ u →
        ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ r ∈ Icc t T, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j (((H.terminalFlow P04).metric r).pullbackCoefficients
              (centeredNeckLift N z.1 z.2)) 0 -
            iteratedFDeriv ℝ j (((H.terminalFlow P04).metric t).pullbackCoefficients
              (centeredNeckLift N z.1 z.2)) 0‖ ≤ B * (r - t) := by
  obtain ⟨sK, hsK, hsKT, hcurv⟩ := H.exists_terminalFlow_curvature_derivative_tail_on_compact P04 hA
  choose K hK hcurv using hcurv
  obtain ⟨sG, hsG, hsGT, hmetric⟩ := H.exists_terminalFlow_pairwise_metric_tail P04 hA
  obtain ⟨Z, hZ, hinit⟩ := exists_centeredNeck_initial_jet_bound.{u} m
  obtain ⟨B, hB, htime⟩ := SpacetimeBounds.exists_closed_terminal_spatialJet_time_constant
    3 m K (fun _ => Z / l) (fun j => (hK j).le)
    (a := 1 / (8 * u)) (b := 12 / l) (by positivity) (by positivity)
  obtain ⟨s, hs, hsT⟩ := exists_between
    (max_lt hsKT (max_lt hsGT (by linarith : T - 1 < T)))
  have hssK : sK < s := (le_max_left _ _).trans_lt hs
  have hssG : sG < s := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  have hsone : T - 1 < s := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  refine ⟨s, B, hsK.trans hssK, hsT, hB, ?_⟩
  intro t ht N hNε hNA hql hqu z hz r hr j hj
  let f := centeredNeckLift N z.1 z.2
  let U := centeredNeckDomain N z.2
  have hU : IsOpen U := centeredNeckDomain_isOpen N z.2
  have hzero : (0 : E) ∈ U := zero_mem_centeredNeckDomain N hz
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    fun p hp => (centeredNeckLift_contMDiffAt N z.1 z.2 hp).contMDiffWithinAt
  have hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    fun _ hy => centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hy
  have hpointA : f 0 ∈ A := hNA (centeredNeckLift_mem N z.1 z.2 hzero)
  let q := N.connection.scalarCurvature N.center
  have hq : 0 < q := N.scalar_center_pos
  have htG : t ∈ Ico sG T := ⟨hssG.le.trans ht.1, ht.2⟩
  have hell : ∀ vtime ∈ Ico t T, ∀ v : E,
      (1 / (8 * u)) * ‖v‖ ^ 2 ≤
          ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v ∧
        ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v ≤
          (12 / l) * ‖v‖ ^ 2 := by
    intro vtime hvtime v
    have hquad := normalizedNeckMetric_centered_ellipticity N (hNε ▸ hε) z hz v
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ q * ((H.terminalFlow P04).metric t).pullbackCoefficients
        f 0 v v ∧ q * ((H.terminalFlow P04).metric t).pullbackCoefficients f 0 v v ≤ 3 * ‖v‖ ^ 2 at hquad
    have hnonneg : 0 ≤ ((H.terminalFlow P04).metric t).pullbackCoefficients f 0 v v := by
      nlinarith [sq_nonneg ‖v‖]
    have hupper := mul_le_mul_of_nonneg_right hqu hnonneg
    have hlower := mul_le_mul_of_nonneg_right hql hnonneg
    have hvG : vtime ∈ Ico sG T := ⟨htG.1.trans hvtime.1, hvtime.2⟩
    have htr := hmetric t htG vtime hvG _ hpointA (mfderiv (𝓡 3) (𝓡 3) f 0 v)
    have hrt := hmetric vtime hvG t htG _ hpointA (mfderiv (𝓡 3) (𝓡 3) f 0 v)
    change ((H.terminalFlow P04).metric t).pullbackCoefficients f 0 v v ≤
      4 * ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v at htr
    change ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v ≤
      4 * ((H.terminalFlow P04).metric t).pullbackCoefficients f 0 v v at hrt
    constructor
    · rw [one_div_mul_eq_div]
      apply (div_le_iff₀ (by positivity : 0 < 8 * u)).mpr
      nlinarith [mul_le_mul_of_nonneg_left htr hu.le]
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hl).mpr
      nlinarith [mul_le_mul_of_nonneg_left hrt hl.le]
  have hinit' : ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (((H.terminalFlow P04).metric t).pullbackCoefficients f) 0‖ ≤ Z / l := by
    intro k hk
    have h := hinit N (by rw [hNε]; linarith) (hNε ▸ hm) z hz k hk
    rw [normalizedNeckMetric_centered_jet N z hz, norm_smul,
      Real.norm_eq_abs, abs_of_pos N.scalar_center_pos] at h
    apply (le_div_iff₀ hl).mpr
    have hscale := mul_le_mul_of_nonneg_right hql
      (norm_nonneg (iteratedFDeriv ℝ k (((H.terminalFlow P04).metric t).pullbackCoefficients f) 0))
    nlinarith
  exact htime (H.terminalFlow P04) hU hf hinv
    ((hsK.trans hssK).trans_le ht.1) ht.2 (by linarith [ht.1]) hzero hell
    (fun k _ vtime hvtime => hcurv k vtime
      ⟨hssK.le.trans (ht.1.trans hvtime.1), hvtime.2⟩ _ hpointA) hinit' r hr j hj

end PoincareConjecture.SingularTimeAssumptions
