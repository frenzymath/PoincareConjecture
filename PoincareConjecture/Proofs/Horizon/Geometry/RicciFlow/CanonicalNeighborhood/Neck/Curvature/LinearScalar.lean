import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.ScalarContraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.InverseBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.BilinearJetBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.ModelJetBounds













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

open SpacetimeBounds

private theorem normalized_realization_scalar_sub_one_le
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000000)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) :
    |D.scalarCurvature 0 - 1| ≤ 1000000000000 * N.epsilon := by
  let J := metricTwoJet h.euclideanCoefficients 0
  let J₀ := metricTwoJet roundCylinderEuclideanCoefficients 0
  let δ := 19044 * N.epsilon
  have hNε := N.epsilon_pos
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by dsimp only [δ]; linarith
  have hscalar (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
      ‖iteratedFDeriv ℝ r (fun x => h.euclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤
        2116 * N.epsilon := by
    have he : (fun x => h.euclideanCoefficients x
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
          roundCylinderEuclideanCoefficients x
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) =ᶠ[𝓝 0]
        (fun x => N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
            roundCylinderEuclideanCoefficients x
              (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
      filter_upwards [heq] with x hx
      rw [hx]
    rw [(he.iteratedFDeriv ℝ r).self_of_nhds]
    exact N.normalizedEuclideanCoefficients_scalar_twoJet_le q hs r hr i j
  obtain ⟨hzero, hone, htwo⟩ := cylinder_metric_twoJet_norm_sub_le
    (h.contDiffAt_euclideanCoefficients 0)
    contDiff_roundCylinderEuclideanCoefficients.contDiffAt hscalar
  have hzero' : ‖J.1 - J₀.1‖ ≤ δ := by
    exact hzero.trans_eq (by dsimp only [δ]; ring)
  have hsmall : ‖J.1 - roundCylinderEuclideanCoefficients 0‖ ≤ 1 / 2 := hzero'.trans hδhalf
  have hg : ‖J.1‖ ≤ 3 := by
    have hn := norm_add_le (J.1 - J₀.1) J₀.1
    rw [sub_add_cancel] at hn
    have hm := roundCylinderEuclideanCoefficients_norm_zero_le
    change ‖J₀.1‖ ≤ 2 at hm
    linarith only [hn, hm, hzero', hδhalf]
  have hi := roundCylinderEuclideanCoefficients_perturbation_inverse_norm_le hsmall
  have hi₀ := roundCylinderEuclideanCoefficients_inverse_norm_zero_le
  have hdi : ‖J.1.inverse - J₀.1.inverse‖ ≤ 2 * δ :=
    (roundCylinderEuclideanCoefficients_perturbation_inverse_sub_norm_le hsmall).trans
      (mul_le_mul_of_nonneg_left hzero' (by norm_num))
  have hfirst₀ : J₀.2.1 = 0 := fderiv_roundCylinderEuclideanCoefficients_zero
  have hfirst : ‖J.2.1‖ ≤ δ := by
    have hh : ‖J.2.1 - J₀.2.1‖ ≤ δ := by
      exact hone.trans_eq (by dsimp only [δ]; ring)
    simpa only [hfirst₀, sub_zero] using hh
  have hsecond : ‖J.2.2 - J₀.2.2‖ ≤ δ := by
    exact htwo.trans_eq (by dsimp only [δ]; ring)
  have hsecond₀ : ‖J₀.2.2‖ ≤ 1000 :=
    norm_second_fderiv_roundCylinderEuclideanCoefficients_zero_le.trans (by norm_num)
  have hbound := scalarTwoJet_sub_le (J := J) (J₀ := J₀) (δ := δ) (K := 1000)
    hδ (hδhalf.trans (by norm_num)) hg hi hi₀ hdi
    hfirst hfirst₀ hsecond hsecond₀
  have hJ : M34.scalarTwoJet J = D.scalarCurvature 0 := M34.scalarTwoJet_metricTwoJet D 0
  have hJ₀ : M34.scalarTwoJet J₀ = 1 := by
    rw [show J₀ = metricTwoJet roundCylinderEuclideanMetric.euclideanCoefficients 0 from rfl,
      M34.scalarTwoJet_metricTwoJet roundCylinderEuclideanMetric.euclideanLeviCivitaData,
      roundCylinderEuclideanMetric_scalarCurvature]
  rw [hJ, hJ₀] at hbound
  dsimp only [δ] at hbound
  nlinarith only [hbound, hNε]



theorem scalarCurvature_sub_one_le
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (D : LeviCivitaData g)
    (hε : N.epsilon ≤ 1 / 1000000) (x : M) (hx : x ∈ N.carrier) :
    |N.scale ^ 2 * D.scalarCurvature x - 1| ≤ 1000000000000 * N.epsilon := by
  let z := N.coordinate_inverse x
  have hz := N.coordinate_inverse_mem x hx
  obtain ⟨h, Dh, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization z.1 hz.2
  have hbound := normalized_realization_scalar_sub_one_le N hε z.1 hz.2 Dh heq
  rw [(N.normalized_realization_curvature D z.1 hz.2 Dh heq).1] at hbound
  simpa only [z, Prod.mk.eta, N.coordinate_map_coordinate_inverse hx] using hbound



theorem exists_linear_scalarCurvature_control :
    ∃ A ε₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
        ∀ x ∈ N.carrier, |N.scale ^ 2 * D.scalarCurvature x - 1| ≤ A * N.epsilon := by
  refine ⟨1000000000000, 1 / 1000000, by norm_num, by norm_num, by norm_num, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε x hx
  exact N.scalarCurvature_sub_one_le D hε x hx

end PoincareConjecture.EpsilonNeck
