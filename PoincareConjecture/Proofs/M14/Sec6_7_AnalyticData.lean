import PoincareConjecture.Proofs.M14.Sec6_7_FixedSourceMonotonicity
import PoincareConjecture.Proofs.M14.Sec6_7_ReducedVolumeAssembly

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point}

noncomputable def reducedVolumeAnalyticDataWithBasis
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) : M14ReducedVolumeAnalyticData G T τ x E H := by
  let D := rescalingMeasureDataWithBasis H b hb
  have hbound := fun Z hZ =>
    stableDensity_mul_jacobian_le_gaussian hCoordinates hM04 hM12 E H D (Z := Z) hZ
  have hi := stableDensity_integrable_of_gaussian hM04 hM12 H D hbound
  refine {
    density := stableReducedVolumeDensity H
    density_eq := fun _ hq => stableReducedVolumeDensity_eq H hq
    density_measurable_on_image :=
      (stableReducedVolumeDensity_measurable hM04 hM12 H).comp measurable_subtype_coe
    density_nonnegative := fun q _ => stableReducedVolumeDensity_nonneg H q
    measure_data := D
    initial_density := fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)
    initial_density_eq := fun _ => rfl
    gaussian_bound := hbound
    density_integrable := hi.2.1
    density_integrable_on_source := hi.1
    density_change_of_variables_on_image := hi.2.2
    backward_star := ?_
    fixed_W_monotone := ?_ }
  · intro W hW Z hZ
    exact stableSet_backward_star hCoordinates hM04 hM12 E H (hW hZ)
  · intro W hW _ _ hm _ σ hσ hle
    exact stableDensity_fixed_source_mono hCoordinates hM04 hM12 E H b hb hW hm hσ hle

theorem reducedVolumeAnalyticData
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E) :
    Nonempty (M14ReducedVolumeAnalyticData G T τ x E H) := by
  obtain ⟨b, hb⟩ := exists_orthonormal_horizontalBasis G x
  exact ⟨reducedVolumeAnalyticDataWithBasis hCoordinates hM04 hM12 E H b hb⟩

theorem reducedVolumeStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) : M14ReducedVolumeStatement G :=
  reducedVolumeStatement_of_analytic hCoordinates hM04 hM12
    (fun _ _ _ E H => reducedVolumeAnalyticData hCoordinates hM04 hM12 E H)

end PoincareConjecture.M14
