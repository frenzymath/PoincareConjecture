import PoincareConjecture.Proofs.M45.Ch9_Models.NormalizedChart
import PoincareConjecture.Proofs.M45.Ch9_Models.MetricRealization
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_NeckFourJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M45

open PoincareConjecture.M44 PoincareConjecture.M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable def modelNeckCoordinateBound : ℝ :=
  Classical.choose exists_centeredCylinderMetric_fourJet_bound

theorem model_four_jet_order {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) :
    epsilon ≤ 1 / 36 ∧ 4 ≤ ⌊epsilon⁻¹⌋₊ := by
  refine ⟨by linarith, ?_⟩
  have hinv : (4 : ℝ) ≤ epsilon⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hepsilon]
    linarith
  exact Nat.le_floor hinv

theorem model_neck_analytic
    {Cg Ce : ℝ} (hCg : 0 < Cg) (hCe : 0 < Ce)
    (hgradient : ∀ (gE : RiemannianMetric 3 E) (DE : LeviCivitaData gE),
      (∀ j ≤ 4, ‖iteratedFDeriv ℝ j gE.euclideanCoefficients 0‖ ≤
        modelNeckCoordinateBound) →
      (∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gE.inner 0 v v) →
      ∀ v : E, gE.inner 0 v v = 1 → |fderiv ℝ DE.scalarCurvature 0 v| ≤ Cg)
    (hevolution : ∀ (gE : RiemannianMetric 3 E) (DE : LeviCivitaData gE),
      (∀ j ≤ 4, ‖iteratedFDeriv ℝ j gE.euclideanCoefficients 0‖ ≤
        modelNeckCoordinateBound) →
      (∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gE.inner 0 v v) →
      |DE.laplacian DE.scalarCurvature 0 + 2 * DE.ricciNormSq 0| ≤ Ce)
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 200) :
    M45PointwiseAnalyticEstimate g D N.center (max Cg Ce) := by
  have hB := (Classical.choose_spec exists_centeredCylinderMetric_fourJet_bound).2 N.epsilon_pos
  obtain ⟨hepsilon, horder⟩ := model_four_jet_order N.epsilon_pos hsmall
  let z := N.coordinate_inverse N.center
  have hcenter : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem N.center hcenter).2
  let f := centeredNeckLift N z.1 z.2
  let U := centeredNeckDomain N z.2
  have hU : IsOpen U := centeredNeckDomain_isOpen N z.2
  have hzero : (0 : E) ∈ U := zero_mem_centeredNeckDomain N hz
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U := fun y hy =>
    (centeredNeckLift_contMDiffAt N z.1 z.2 hy).contMDiffWithinAt
  have hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    fun y hy => centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hy
  obtain ⟨gE, DE, W, hW, hzeroW, hWU, hmetric⟩ :=
    model_metric_realization g hU hzero hf hinv
  let Q := N.connection.scalarCurvature N.center
  have hQ : 0 < Q := N.scalar_center_pos
  let gQ := m01RescaledMetric gE Q hQ
  let DQ := m01RescaledMetric_connection gE DE Q hQ
  have hcoeff : gQ.euclideanCoefficients =ᶠ[𝓝 0]
      centeredCylinderMetric (fun q v w => normalizedNeckForm N q v w) z.1 z.2 := by
    filter_upwards [hW.mem_nhds hzeroW] with y hy
    calc
      gQ.euclideanCoefficients y = Q • gE.euclideanCoefficients y := rfl
      _ = Q • g.pullbackCoefficients f y := congrArg (fun B => Q • B) (hmetric y hy)
      _ = (normalizedNeckMetric N).pullbackCoefficients f y := rfl
      _ = _ := normalizedNeckMetric_pullbackCoefficients N z.1 z.2 (hWU hy)
  have hclose : RoundCylinderClose N.epsilon 0 (fun q v w => normalizedNeckForm N q v w) :=
    N.metric_comparison.close
  have hjets : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j gQ.euclideanCoefficients 0‖ ≤
      modelNeckCoordinateBound := by
    intro j hj
    rw [(hcoeff.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
    exact hB (by linarith) hclose horder z hz j hj
  have hell : ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gQ.inner 0 v v := by
    intro v
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gQ.euclideanCoefficients 0 v v
    rw [hcoeff.self_of_nhds]
    exact centeredCylinderMetric_lower N.epsilon_pos hepsilon hclose (by omega) z hz v
  have hgeom (y : E) (hy : y ∈ W) (v w : E) :
      gE.inner y v w = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) :=
    congrArg (fun B => B v w) (hmetric y hy)
  have hfzero : f 0 = N.center := by
    rw [show f 0 = N.coordinate_map (z.1, z.2) from centeredNeckLift_zero N z.1 z.2]
    exact neck_coordinate_inverse N hcenter
  have hscalar : Q ≤ D.scalarCurvature (f 0) := by
    have hsame := N.connection.scalarCurvature_eq_of_local_isometry D (f := id)
      isOpen_univ contMDiff_id.contMDiffOn
      (fun y _ v w => by simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq])
      (mem_univ N.center)
    simp only [id_eq] at hsame
    rw [hfzero, ← hsame]
  have h := model_analytic_of_normalized_chart D gE DE hQ hCg hCe hW hzeroW
    (hf.mono hWU) (fun y hy => hinv y (hWU hy)) hgeom hscalar
    (hgradient gQ DQ hjets hell) (hevolution gQ DQ hjets hell)
  simpa only [hfzero] using h

end PoincareConjecture.M45
