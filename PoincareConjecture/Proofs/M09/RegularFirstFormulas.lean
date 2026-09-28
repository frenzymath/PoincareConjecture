import PoincareConjecture.Proofs.M09.RegularBranchFirstDerivatives
import PoincareConjecture.Proofs.M09.HarnackIntegral
import PoincareConjecture.Proofs.M09.HarnackCongruence








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialGeometry_first_formulas {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p : M} (G : LExponentialGeometry F T τmax p)
    (z : M × ℝ) (hz : z ∈ G.regularImage) :
    let r := G.regular_point z hz
    deriv (fun s ↦ r.representative (z.1, s)) z.2 =
        (F.connection (T - z.2)).scalarCurvature z.1 - r.representative z / z.2 +
          reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative z.2 /
            (2 * z.2 * Real.sqrt z.2) ∧
      reducedLengthGradientNormSq F T r.representative z.2 z.1 =
        r.representative z / z.2 -
          reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative z.2 /
            (z.2 * Real.sqrt z.2) - (F.connection (T - z.2)).scalarCurvature z.1 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let Z := (G.regular_chart.symm z).1
  let r := G.regular_point z hz
  have hb := r.tau_pos
  have hmax := r.tau_lt
  have hsrc : (Z, z.2) ∈ G.regular_chart.source := by
    have h := G.regular_chart.map_target hz
    change ((G.regular_chart.symm z).1, (G.regular_chart.symm z).2) ∈ G.regular_chart.source at h
    rwa [G.regular_inverse_time z hz] at h
  have hend : G.gamma Z z.2 = z.1 := by
    have h := congrArg Prod.fst ((G.regular_forward (G.regular_chart.symm z)).symm.trans
      (G.regular_chart.right_inv hz))
    simpa only [G.regular_inverse_time z hz] using h
  obtain ⟨_, hgrad, htime⟩ := lExponentialFamily_regular_branch_first_derivatives
    hM04 hτmax hwindow hL G.toLExponentialFamily G.regular_chart G.regular_source
    G.regular_forward G.regular_target_times G.regular_inverse_smooth Z z.2 hsrc
  have hrep := G.regular_point_representative z hz
  rw [← hrep, hend] at hgrad htime
  have hpath := G.regular_point_path z hz
  have hK := (regular_harnackIntegral_eq_family hM04 hwindow r G.toLExponentialFamily Z hpath).trans
    (lExponentialFamily_harnack_integral_eq hM04 hτmax hwindow G.toLExponentialFamily Z z.2 hb hmax)
  rw [hend] at hK
  have hvalue := regular_representative_eq_family_action r G.toLExponentialFamily Z hpath
  change r.representative z = G.toLExponentialFamily.action Z z.2 / (2 * Real.sqrt z.2) at hvalue
  change deriv (fun s ↦ r.representative (z.1, s)) z.2 = _ ∧
    reducedLengthGradientNormSq F T r.representative z.2 z.1 = _
  constructor
  · rw [htime, hK, hvalue]
    field_simp [hb.ne', (Real.sqrt_pos.mpr hb).ne']
    ring
  · rw [hgrad, hK, hvalue]
    field_simp [hb.ne', (Real.sqrt_pos.mpr hb).ne']
    ring

set_option backward.isDefEq.respectTransparency false in
theorem regular_first_formulas_on_regularImage {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p q : M} {b : ℝ}
    (G : LExponentialGeometry F T τmax p) (hz : (q, b) ∈ G.regularImage)
    (r : ReducedLengthRegularPoint F T τmax p q b) :
    deriv (fun s ↦ r.representative (q, s)) b =
        (F.connection (T - b)).scalarCurvature q - r.representative (q, b) / b +
          reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative b /
            (2 * b * Real.sqrt b) ∧
      reducedLengthGradientNormSq F T r.representative b q =
        r.representative (q, b) / b -
          reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative b /
            (b * Real.sqrt b) - (F.connection (T - b)).scalarCurvature q := by
  let s := G.regular_point (q, b) hz
  let Z := (G.regular_chart.symm (q, b)).1
  have heq : r.representative =ᶠ[𝓝 (q, b)] s.representative := by
    filter_upwards [r.neighborhood_open.mem_nhds r.center_mem,
      s.neighborhood_open.mem_nhds s.center_mem] with z hzr hzs
    exact (r.representative_eq z hzr).trans (s.representative_eq z hzs).symm
  have hvalue := heq.self_of_nhds
  have htime : deriv (fun t ↦ r.representative (q, t)) b =
      deriv (fun t ↦ s.representative (q, t)) b :=
    (heq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt).deriv_eq
  have hspace : mvfderiv (𝓡 n) (fun x ↦ r.representative (x, b)) q =
      mvfderiv (𝓡 n) (fun x ↦ s.representative (x, b)) q :=
    (heq.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt).mfderiv_eq
  have hgrad : reducedLengthGradientNormSq F T r.representative b q =
      reducedLengthGradientNormSq F T s.representative b q := by
    simp only [reducedLengthGradientNormSq, hspace]
  have hpath : Set.EqOn r.path.curve (G.gamma Z) (Set.Icc 0 b) := by
    have h := r.unique_minimizing_path s.path s.path_start s.path_end s.minimizing
    exact h.symm.trans (G.regular_point_path (q, b) hz)
  have hK : reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative b =
      reducedHarnackIntegral F T s.path.curve s.path_scalar_time_derivative b :=
    (regular_harnackIntegral_eq_family hM04 hwindow r G.toLExponentialFamily Z hpath).trans
      (regular_harnackIntegral_eq_family hM04 hwindow s G.toLExponentialFamily Z
        (G.regular_point_path (q, b) hz)).symm
  rw [htime, hgrad, hvalue, hK]
  exact lExponentialGeometry_first_formulas hM04 hτmax hwindow hL G (q, b) hz

end PoincareConjecture.Proofs.M09
