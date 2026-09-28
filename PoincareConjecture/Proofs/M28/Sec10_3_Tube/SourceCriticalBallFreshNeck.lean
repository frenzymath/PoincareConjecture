import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshMetricError
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.VaryingScaleReadout
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.RawError











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open tube PoincareConjecture.Proofs.M28.NeckTransfer PoincareConjecture.Proofs.M28.NeckAnalysis
open PoincareConjecture.Proofs.M28.FiniteHessian

set_option maxHeartbeats 3200000 in




theorem exists_retained_fresh_neck
    {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)}
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
      0 < D0.scalarCurvature q → epsilon < 1 / 3 →
      ∀ (sigma : ℕ → ℕ), StrictMono sigma →
      ∀ (N : ∀ k, EpsilonNeck
        ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time)),
        (∀ k, (N k).epsilon = epsilon) →
        (∀ k, (N k).center = (G.embedding (sigma k) q).val.val) →
        Tendsto (fun k =>
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
            ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
              (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩ *
                (N k).scale ^ 2) atTop (𝓝 (D0.scalarCurvature q)⁻¹) →
        ∀ j : ℕ, (∀ᶠ k in atTop, j ≤ sigma k ∧ ∀ x ∈ (N k).carrier,
          |((N k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
            x ∈ (fun y => (G.embedding (sigma k) y).val.val) '' G.exhaustion j) →
          ∀ᶠ k in atTop, j ≤ sigma k ∧ ∃ V : EpsilonNeck G.limitMetric,
            V.epsilon = 3 * epsilon / 2 ∧ V.center = q ∧
            V.scale = (D0.scalarCurvature q) ^ (-1 / 2 : ℝ) ∧ V.connection = D0 ∧
            V.carrier ⊆ G.exhaustion j ∧ ∀ z : RoundCylinderSpace,
              V.coordinate_map z =
                (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                  W.high_index G (sigma k)).symm ((N k).coordinate_map z) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q hscalar hsmall sigma hsigma N heps hcenter hconv j hcapture
  have hepspos : 0 < epsilon := heps 0 ▸ (N 0).epsilon_pos
  let eta := 3 * epsilon / 2
  let m := ⌊eta⁻¹⌋₊
  let a := (D0.scalarCurvature q)⁻¹
  let rstar := (D0.scalarCurvature q) ^ (-1 / 2 : ℝ)
  have ha : 0 < a := inv_pos.mpr hscalar
  have hrstar : 0 < rstar := Real.rpow_pos_of_pos hscalar _
  have hrstarSq : rstar ^ 2 = a := by
    dsimp only [rstar, a]
    rw [← Real.rpow_mul_natCast hscalar.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  have hepseta : epsilon < eta := by dsimp only [eta]; linarith
  have heta : 0 < eta := hepspos.trans hepseta
  have hetahalf : eta < 1 / 2 := by dsimp only [eta]; linarith
  have hmpos : 1 ≤ m := (Nat.one_le_floor_iff _).mpr
    ((one_le_inv₀ heta).mpr (by linarith))
  obtain ⟨n, hnm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have horder : m ≤ ⌊epsilon⁻¹⌋₊ := cylinderOrder_mono hepspos hepseta.le
  have hn : n + 1 ≤ ⌊epsilon⁻¹⌋₊ := by omega
  have hscales := (hconv.eventually
    (eventually_ge_nhds (show a / 2 < a from half_lt_self ha))).and
      (hconv.eventually (eventually_le_nhds (show a < 2 * a by linarith)))
  have hgeometry := H.exists_retained_fresh_geometry W G D0 q hscalar hsmall sigma
    hsigma N heps hcenter j hcapture
  obtain ⟨delta, hdelta, hperturb⟩ :=
    exists_roundCylinderClose_perturbation_tolerance hepspos hepseta
  obtain ⟨rho, hrho, hraw⟩ := exists_cylinder_raw_error_tolerance m hdelta
  let L := cylinderScalarCoordinateEquiv.symm.toContinuousLinearMap
  let F := rstar⁻¹ ^ 2 * (max 1 ‖L‖) ^ m
  have hF : 0 < F := mul_pos (pow_pos (inv_pos.mpr hrstar) 2)
    (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) m)
  have hbudget : 0 < rho / (2 * F) := div_pos hrho (mul_pos (by norm_num) hF)
  obtain ⟨Kmetric, hKmetric⟩ := H.exists_retained_fresh_metric_error W G sigma hsigma N
    heps hsmall (a / 2) (2 * a) (half_pos ha) hscales j hcapture n hn
    (rho / (2 * F)) hbudget
  let I := {z : ℕ × RoundCylinderSpace // z.2.2 ∈ Ioo (-eta⁻¹) eta⁻¹}
  have hs (i : I) : i.1.2.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    cylinderStrip_mono hepspos hepseta.le i.2
  have hjets := hasUniformJetBoundsAt_cylinderNeckCoefficients (fun i : I => N i.1.1)
    hepspos (by linarith) (fun i => heps i.1.1) m horder
    (fun i => i.1.2.1) (fun i => i.1.2.2) hs
  have hc (i : I) : ContDiffAt ℝ ∞
      (cylinderNeckCoefficients (N i.1.1) i.1.2.1 i.1.2.2) 0 := by
    apply (contDiffOn_cylinderNeckCoefficients (N i.1.1) i.1.2.1 i.1.2.2).contDiffAt
    apply (isOpen_cylinderNeckChartDomain (N i.1.1) i.1.2.1 i.1.2.2).mem_nhds
    apply zero_mem_cylinderNeckChartDomain
    simpa only [heps] using hs i
  obtain ⟨Kscale, hKscale⟩ := hjets.exists_scalar_error_tail hc hconv (fun i => i.1.1)
    (rho / (2 * F)) hbudget
  filter_upwards [hgeometry, eventually_ge_atTop (max Kmetric Kscale)] with k hk hkK
  obtain ⟨hjk, V, hcenterV, hscaleV, hconnection, hcarrier, hmap⟩ := hk
  let idx := W.high_index (G.subsequence (sigma k))
  let Q := (E (idx + H.shift)).flow.scalar
    ⟨(E (idx + H.shift)).time, (E (idx + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos idx
  let S : RoundCylinderTwoTensor := fun z v w => (N k).scale⁻¹ ^ 2 *
    roundCylinderPullback ((E (idx + H.shift)).flow.metric
      (E (idx + H.shift)).time) (N k).coordinate_map z v w
  have hsource : RoundCylinderClose epsilon 0 S := by
    have hh := (N k).metric_comparison.close
    rw [heps] at hh
    exact hh
  have hclose : RoundCylinderClose eta 0 V.tensor := by
    apply hperturb 0 (by norm_num) V.tensor S hsource V.tensor_smooth
    intro z hz
    apply hraw eta V.tensor S V.tensor_smooth
      (hsource.1.mono_epsilon_m28 hepspos hepseta.le) z hz
    intro r hr a0 b0
    have hsN : z.2 ∈ Ioo (-(N k).epsilon⁻¹) (N k).epsilon⁻¹ := by
      rw [heps]
      exact cylinderStrip_mono hepspos hepseta.le hz
    have h := V.norm_frozen_difference_jet_le_of_scale_error (N k) Q hQ z.1 hz hsN a0 b0 r
    have hlocal : V.coordinate_map ∘
        (cylinderSphereParametrization z.1 ∘ cylinderScalarCoordinates z.2) =
          capturedCylinderMap
            (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
              W.high_index G (sigma k)) (N k) z.1 z.2 := by
      funext x
      exact hmap _
    rw [hlocal, hscaleV, hrstarSq] at h
    have hmetric : ‖iteratedFDeriv ℝ r (fun x => G.limitMetric.pullbackCoefficients
        (capturedCylinderMap
          (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k)) (N k) z.1 z.2) x -
        RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric _ Q hQ)
          (cylinderNeckChart (N k) z.1 z.2) x) 0‖ ≤ rho / (2 * F) :=
      hKmetric k ((le_max_left _ _).trans hkK) z hz r (by omega)
    have hscaleError : ‖iteratedFDeriv ℝ r (fun x =>
        (Q * (N k).scale ^ 2 - a) • cylinderNeckCoefficients (N k) z.1 z.2 x) 0‖ ≤
          rho / (2 * F) :=
      hKscale ⟨(k, z), hz⟩ ((le_max_right _ _).trans hkK) r hr
    have hsum := add_le_add hmetric hscaleError
    have hbudget_eq : rho / (2 * F) + rho / (2 * F) = rho / F := by ring
    rw [hbudget_eq] at hsum
    have hpower : ‖L‖ ^ r ≤ (max 1 ‖L‖) ^ m :=
      (pow_le_pow_left₀ (norm_nonneg L) (le_max_right _ _) r).trans
        (pow_le_pow_right₀ (le_max_left _ _) hr)
    have hfactor : rstar⁻¹ ^ 2 * ‖L‖ ^ r ≤ F :=
      mul_le_mul_of_nonneg_left hpower (sq_nonneg _)
    exact h.trans ((mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))).trans
        ((mul_le_mul_of_nonneg_right hfactor (div_pos hrho hF).le).trans_eq
          (mul_div_cancel₀ rho hF.ne')))
  exact ⟨hjk, V.toEpsilonNeck hclose, rfl, hcenterV, hscaleV, hconnection, hcarrier, hmap⟩

set_option maxHeartbeats 3200000 in





theorem exists_retained_positive_limit_neck_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
            (L : EpsilonNeck G.limitMetric), L.center = G.base →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              (∀ᶠ k in atTop, (G.embedding (sigma k) q).val.val ∉
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) →
              ∃ N : EpsilonNeck G.limitMetric, N.epsilon = 3 * epsilon / 2 ∧
                N.center = q ∧ N.connection = D0 ∧
                  ∃ j : ℕ, N.carrier ⊆ G.exhaustion j := by
  obtain ⟨epsilon0, hpos, hsmall, hcore⟩ :=
    exists_retained_strong_neck_core_capture_accuracy P
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q L hL sigma hsigma f hf hbound hgraphs hside
  obtain ⟨J, hcenter, ha, hconv, j, hcapture⟩ :=
    hcore H W hepsilon G D0 q L hL sigma hsigma f hf hbound hgraphs hside
  have hthird : epsilon < 1 / 3 := (hepsilon.trans hsmall).trans_lt (by norm_num)
  have hhalf : epsilon < 1 / 2 := hthird.trans (by norm_num)
  let N := fun k => strongNeck_top (J k) hhalf
  obtain ⟨k, hk⟩ := (H.exists_retained_fresh_neck W G D0 q (inv_pos.mp ha) hthird
    sigma hsigma N (fun _ => rfl) hcenter hconv j hcapture).exists
  obtain ⟨_, V, hepsV, hcenterV, _hscaleV, hconnectionV, hcarrierV, _hmapV⟩ := hk
  exact ⟨V, hepsV, hcenterV, hconnectionV, j, hcarrierV⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
