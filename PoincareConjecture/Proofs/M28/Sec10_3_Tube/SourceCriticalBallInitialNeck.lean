import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialMetricError
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.CoreCoefficientReadout
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.RawError










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open tube PoincareConjecture.Proofs.M28.NeckTransfer PoincareConjecture.Proofs.M28.NeckAnalysis

set_option maxHeartbeats 2400000 in





theorem exists_retained_initial_neck_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∀ (W : CriticalBallSourcePacket H)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
            (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ D₀ : LeviCivitaData G.limitMetric, ∃ j : ℕ, ∀ᶠ k in atTop,
            j ≤ k ∧ ∃ N : EpsilonNeck G.limitMetric,
              N.epsilon = 3 * epsilon / 2 ∧ N.center = G.base ∧
              N.scale = (4 * max C 2)⁻¹ ∧ N.connection = D₀ ∧
              N.carrier ⊆ G.exhaustion j ∧ ∀ z : RoundCylinderSpace,
                N.coordinate_map z =
                  (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                    W.high_index G k).symm
                      (((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map
                        z) := by
  obtain ⟨epsilonG, hGpos, hGsmall, hgeometry⟩ := exists_retained_initial_geometry_accuracy.{u}
  obtain ⟨epsilonE, hEpos, _, herror⟩ := exists_retained_initial_metric_error_accuracy.{u}
  refine ⟨min epsilonG epsilonE, lt_min hGpos hEpos,
    (min_le_left _ _).trans hGsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀
  have hepsG := hepsilon.trans (min_le_left _ _)
  have hepsE := hepsilon.trans (min_le_right _ _)
  obtain ⟨j, hj⟩ := hgeometry H hepsG W G D₀
  have hepspos : 0 < epsilon :=
    (H.segment 0).cover_epsilon ▸ (H.segment 0).cover.epsilon_pos
  let eta := 3 * epsilon / 2
  let m := ⌊eta⁻¹⌋₊
  let s₀ := (4 * max C 2)⁻¹
  have hepseta : epsilon < eta := by dsimp only [eta]; linarith
  have heta : 0 < eta := hepspos.trans hepseta
  have hetahalf : eta < 1 / 2 := by dsimp only [eta]; linarith [hepsG.trans hGsmall]
  have hmpos : 1 ≤ m := (Nat.one_le_floor_iff _).mpr
    ((one_le_inv₀ heta).mpr (by linarith))
  obtain ⟨n, hnm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hn : n + 1 ≤ ⌊epsilon⁻¹⌋₊ := by
    have horder : m ≤ ⌊epsilon⁻¹⌋₊ := cylinderOrder_mono hepspos hepseta.le
    omega
  have hs₀ : 0 < s₀ := by
    have hC : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
    dsimp only [s₀]
    positivity
  obtain ⟨delta, hdelta, hperturb⟩ :=
    exists_roundCylinderClose_perturbation_tolerance hepspos hepseta
  obtain ⟨rho, hrho, hraw⟩ := exists_cylinder_raw_error_tolerance m hdelta
  let L := cylinderScalarCoordinateEquiv.symm.toContinuousLinearMap
  let F := s₀⁻¹ ^ 2 * (max 1 ‖L‖) ^ m
  have hF : 0 < F := by
    have hmax : 0 < max 1 ‖L‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact mul_pos (pow_pos (inv_pos.mpr hs₀) 2) (pow_pos hmax m)
  obtain ⟨K, hK⟩ := herror H hepsE W G n hn (rho / F) (div_pos hrho hF)
  refine ⟨j, ?_⟩
  filter_upwards [hj, eventually_ge_atTop K] with k hk hkK
  obtain ⟨hjk, V, hcenter, hscale, hconnection, hcarrier, hmap⟩ := hk
  let i := W.high_index (G.subsequence k)
  let N := ((W.tube i).list.node 0).2
  let Q := (E (i + H.shift)).flow.scalar
    ⟨(E (i + H.shift)).time, (E (i + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos i
  have hepsN : N.epsilon = epsilon := (W.tube i).initial_node_geometry.1
  have hscaleN : Q * N.scale ^ 2 = V.scale ^ 2 := by
    rw [hscale]
    exact H.normalizedSlice_initial_scale_sq W.tube i
  let S : RoundCylinderTwoTensor := fun z v w =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback ((E (i + H.shift)).flow.metric
      (E (i + H.shift)).time) N.coordinate_map z v w
  have hsource : RoundCylinderClose epsilon 0 S := by
    have h := N.metric_comparison.close
    rw [hepsN] at h
    exact h
  have hclose : RoundCylinderClose eta 0 V.tensor := by
    apply hperturb 0 (by norm_num) V.tensor S hsource V.tensor_smooth
    intro z hz
    apply hraw eta V.tensor S V.tensor_smooth
      (hsource.1.mono_epsilon_m28 hepspos hepseta.le) z hz
    intro r hr a b
    have hsN : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hepsN]
      exact cylinderStrip_mono hepspos hepseta.le hz
    have h := V.norm_frozen_difference_jet_le N Q hQ hscaleN z.1 hz hsN a b r
    have hlocal : V.coordinate_map ∘
        (cylinderSphereParametrization z.1 ∘ cylinderScalarCoordinates z.2) =
          capturedCylinderMap
            (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k)
            N z.1 z.2 := by
      funext x
      exact hmap _
    rw [hlocal, hscale] at h
    have hmetric : ‖iteratedFDeriv ℝ r (fun x =>
        G.limitMetric.pullbackCoefficients
          (capturedCylinderMap
            (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k)
            N z.1 z.2) x -
        RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric _ Q hQ)
          (cylinderNeckChart N z.1 z.2) x) 0‖ ≤ rho / F :=
      hK k hkK z hz r (by omega)
    have hpower : ‖L‖ ^ r ≤ (max 1 ‖L‖) ^ m :=
      (pow_le_pow_left₀ (norm_nonneg L) (le_max_right _ _) r).trans
        (pow_le_pow_right₀ (le_max_left _ _) hr)
    have hfactor : s₀⁻¹ ^ 2 * ‖L‖ ^ r ≤ F :=
      mul_le_mul_of_nonneg_left hpower (sq_nonneg _)
    exact h.trans ((mul_le_mul_of_nonneg_left hmetric
      (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))).trans
        ((mul_le_mul_of_nonneg_right hfactor (div_pos hrho hF).le).trans_eq
          (mul_div_cancel₀ rho hF.ne')))
  exact ⟨hjk, V.toEpsilonNeck hclose, rfl, hcenter, hscale, hconnection, hcarrier, hmap⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
