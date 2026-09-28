import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.NeckRestriction
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.JetBounds
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.Comparison
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.PullbackSmooth
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.SharedExport

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M28.NeckTransfer

open PoincareConjecture.Proofs.M28.FiniteHessian
open PoincareConjecture.Proofs.M28.NeckAnalysis
open PoincareConjecture.M28

structure NeckGeometryCore
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (epsilon : ℝ) where
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  scale : ℝ
  scale_pos : 0 < scale
  center : M
  connection : LeviCivitaData g
  scalar_center_pos : 0 < connection.scalarCurvature center
  scale_eq_scalar : scale = (connection.scalarCurvature center) ^ (-1 / 2 : ℝ)
  carrier : Set M
  carrier_open : IsOpen carrier
  coordinate : NeckDomain epsilon ≃ₜ carrier
  coordinate_map : UnitTwoSphere × ℝ → M
  coordinate_map_eq : ∀ z : NeckDomain epsilon,
    coordinate z = coordinate_map (z.1, (z.2 : ℝ))
  coordinate_map_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate_map
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)
  coordinate_inverse : M → UnitTwoSphere × ℝ
  coordinate_inverse_mem : ∀ x ∈ carrier,
    coordinate_inverse x ∈ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  coordinate_inverse_left : ∀ z : NeckDomain epsilon,
    coordinate_inverse (coordinate z) = (z.1, (z.2 : ℝ))
  coordinate_inverse_right : ∀ x hx,
    coordinate ((coordinate_inverse x).1,
      ⟨(coordinate_inverse x).2, (coordinate_inverse_mem x hx).2⟩) = ⟨x, hx⟩
  coordinate_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ coordinate_inverse carrier
  central_sphere : Set M
  central_sphere_eq : central_sphere = coordinate_map '' (univ ×ˢ ({0} : Set ℝ))
  center_on_central_sphere : center ∈ central_sphere
  central_sphere_subset : central_sphere ⊆ carrier

noncomputable def NeckGeometryCore.tensor
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : NeckGeometryCore g epsilon) : RoundCylinderTwoTensor :=
  fun z v w => C.scale⁻¹ ^ 2 * roundCylinderPullback g C.coordinate_map z v w

theorem NeckGeometryCore.tensor_smooth
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : NeckGeometryCore g epsilon) :
    RoundCylinderTensorSmoothOn epsilon C.tensor := by
  intro q a b
  have h := roundCylinderPullback_smooth (g := g) (f := C.coordinate_map)
    C.coordinate_map_smooth q a b
  simpa [NeckGeometryCore.tensor, roundCylinderTensorCoefficient, smul_eq_mul]
    using (contDiffOn_const.mul h)

noncomputable def NeckGeometryCore.toEpsilonNeck
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : NeckGeometryCore g epsilon)
    (hclose : RoundCylinderClose epsilon 0 C.tensor) : EpsilonNeck g where
  epsilon := epsilon
  epsilon_pos := C.epsilon_pos
  epsilon_lt_half := C.epsilon_lt_half
  scale := C.scale
  scale_pos := C.scale_pos
  center := C.center
  connection := C.connection
  scalar_center_pos := C.scalar_center_pos
  scale_eq_scalar := C.scale_eq_scalar
  carrier := C.carrier
  carrier_open := C.carrier_open
  coordinate := C.coordinate
  coordinate_map := C.coordinate_map
  coordinate_map_eq := C.coordinate_map_eq
  coordinate_map_smooth := C.coordinate_map_smooth
  coordinate_inverse := C.coordinate_inverse
  coordinate_inverse_mem := C.coordinate_inverse_mem
  coordinate_inverse_left := C.coordinate_inverse_left
  coordinate_inverse_right := C.coordinate_inverse_right
  coordinate_inverse_smooth := C.coordinate_inverse_smooth
  central_sphere := C.central_sphere
  central_sphere_eq := C.central_sphere_eq
  center_on_central_sphere := C.center_on_central_sphere
  central_sphere_subset := C.central_sphere_subset
  metric_comparison := ⟨hclose⟩

noncomputable def normalizedTensor
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X] {h : RiemannianMetric 3 X}
    (N : EpsilonNeck h) : RoundCylinderTwoTensor :=
  fun z v w => (N.scale ^ 2)⁻¹ * roundCylinderPullback h N.coordinate_map z v w

structure PartialLimitNeckExport
    {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {tau : ℝ}
    {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}
    {p : ∀ k, M k} {A : ℝ}
    (E : PartialLimitWindowExport F p A) (epsilon eta : ℝ) where
  sourceNeck : ∀ j, EpsilonNeck ((F (E.limit.subsequence j)).metric 0)
  sourceEpsilon : ∀ j, (sourceNeck j).epsilon = epsilon
  targetCore : letI := E.limit.limitCarrier.topologicalSpace
    letI := E.limit.limitCarrier.chartedSpace
    letI := E.limit.limitCarrier.isManifold
    ∀ _j, NeckGeometryCore E.limit.limitMetric eta
  targetCore_center : letI := E.limit.limitCarrier.topologicalSpace
    letI := E.limit.limitCarrier.chartedSpace
    letI := E.limit.limitCarrier.isManifold
    ∀ j, (targetCore j).center = E.limit.base
  compact_capture : letI := E.limit.limitCarrier.topologicalSpace
    ∀ j, (sourceNeck j).carrier ⊆
      E.limit.embedding j '' E.limit.exhaustion j
  raw_cylinder_jet_convergence : letI := E.limit.limitCarrier.topologicalSpace
    letI := E.limit.limitCarrier.chartedSpace
    letI := E.limit.limitCarrier.isManifold
    ∀ delta : ℝ, 0 < delta →
      ∀ᶠ j in atTop, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
        cylinderJetDifferenceSquared 0 (targetCore j).tensor
          (normalizedTensor (sourceNeck j)) ⌊eta⁻¹⌋₊ z ≤ delta

noncomputable def PartialLimitNeckExport.target_core
    {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {tau : ℝ}
    {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}
    {p : ∀ k, M k} {A epsilon eta : ℝ}
    (E : PartialLimitWindowExport F p A)
    (D : PartialLimitNeckExport E epsilon eta) (j : ℕ) :
    letI := E.limit.limitCarrier.topologicalSpace
    letI := E.limit.limitCarrier.chartedSpace
    letI := E.limit.limitCarrier.isManifold
    NeckGeometryCore E.limit.limitMetric eta :=
  D.targetCore j

theorem eventually_exists_neck_of_partial_limit_export
    {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {tau : ℝ}
    {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}
    {p : ∀ k, M k} {A epsilon eta : ℝ}
    (E : PartialLimitWindowExport F p A)
    (D : PartialLimitNeckExport E epsilon eta)
    (hepsilon : 0 < epsilon) (heta : epsilon < eta)
    (_heta_half : eta < 1 / 2) :
    letI := E.limit.limitCarrier.topologicalSpace
    letI := E.limit.limitCarrier.chartedSpace
    letI := E.limit.limitCarrier.isManifold
    ∀ᶠ j in atTop, ∃ N : EpsilonNeck E.limit.limitMetric,
      N.epsilon = eta ∧ N.center = E.limit.base ∧
        N.connection = (D.targetCore j).connection := by
  letI := E.limit.limitCarrier.topologicalSpace
  letI := E.limit.limitCarrier.chartedSpace
  letI := E.limit.limitCarrier.isManifold
  obtain ⟨delta, hdelta, hperturb⟩ :=
    PoincareConjecture.exists_roundCylinderClose_perturbation_tolerance hepsilon heta
  have hsource : ∀ j, RoundCylinderClose epsilon 0
      (normalizedTensor (D.sourceNeck j)) := by
    intro j
    have hclose := (D.sourceNeck j).metric_comparison.close
    rw [D.sourceEpsilon j] at hclose
    convert hclose using 1
    funext z v w
    simp [normalizedTensor, inv_pow]
  filter_upwards [D.raw_cylinder_jet_convergence delta hdelta] with j hj
  have hclose : RoundCylinderClose eta 0 (D.targetCore j).tensor := by
    apply hperturb 0 (by norm_num) (D.targetCore j).tensor
      (normalizedTensor (D.sourceNeck j)) (hsource j)
      (D.targetCore j).tensor_smooth
    exact hj
  refine ⟨(D.targetCore j).toEpsilonNeck hclose, rfl, ?_, rfl⟩
  exact D.targetCore_center j

structure VaryingSourceTransferData
    (ι : Type*) [Preorder ι] (l : Filter ι)
    (E F : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 M) (sourceMetric : ι → RiemannianMetric 3 X)
    (epsilon eta : ℝ) where
  sourceNeck : ∀ i, EpsilonNeck (sourceMetric i)
  sourceEpsilon : ∀ i, (sourceNeck i).epsilon = epsilon
  sourceEmbedding : ι → M → X
  sourceInverse : ι → X → M
  limitCenter : M
  limitConnection : LeviCivitaData g
  sourceCenter : ∀ᶠ i in l, (sourceNeck i).center = sourceEmbedding i limitCenter
  sourceScalarConverges :
    Tendsto (fun i => (sourceNeck i).connection.scalarCurvature
      (sourceNeck i).center) l
      (𝓝 (limitConnection.scalarCurvature limitCenter))
  compactSet : Set M
  compactSet_compact : IsCompact compactSet
  compactCapture : ∀ᶠ i in l,
    (sourceNeck i).coordinate_map ''
        (univ ×ˢ Ioo (-eta⁻¹) eta⁻¹) ⊆ sourceEmbedding i '' compactSet
  inverse_on_capture : ∀ᶠ i in l, ∀ x ∈ compactSet,
    sourceInverse i (sourceEmbedding i x) = x
  metricJetCompact : Set E
  metricJetCompact_compact : IsCompact metricJetCompact
  metricCoefficient : ι → E → F
  limitMetricCoefficient : E → F
  metricJets : ∀ m : ℕ,
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ m (metricCoefficient i))
      (iteratedFDeriv ℝ m limitMetricCoefficient) l metricJetCompact
  finiteMap : ι → E → F
  finiteMapPoint : ι → E
  finiteMapJets : HasUniformJetBoundsAt n finiteMap finiteMapPoint
  targetCore : ∀ _, NeckGeometryCore g eta
  targetCore_center : ∀ i, (targetCore i).center = limitCenter
  targetCore_connection : ∀ i, (targetCore i).connection = limitConnection
  jetDifference : ∀ delta : ℝ, 0 < delta → ∀ᶠ i in l, ∀ z : RoundCylinderSpace,
    z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
      cylinderJetDifferenceSquared 0 (targetCore i).tensor
        (normalizedTensor (sourceNeck i))
        ⌊eta⁻¹⌋₊ z ≤ delta

theorem eventually_exists_neck_of_transferred_geometry_and_jet_error
    {ι : Type*} [Preorder ι] (l : Filter ι)
    (E F : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 M} {sourceMetric : ι → RiemannianMetric 3 X}
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (heta : epsilon < eta)
    (_heta_half : eta < 1 / 2)
    (D : VaryingSourceTransferData ι l E F n g sourceMetric epsilon eta) :
    ∀ᶠ _i in l, ∃ N : EpsilonNeck g,
      N.epsilon = eta ∧ N.center = D.limitCenter ∧
        N.connection = D.limitConnection := by
  obtain ⟨delta, hdelta, hperturb⟩ :=
    PoincareConjecture.exists_roundCylinderClose_perturbation_tolerance hepsilon heta
  have hdiff_eventual := D.jetDifference delta hdelta
  have hsource : ∀ᶠ i in l,
      RoundCylinderClose epsilon 0 (normalizedTensor (D.sourceNeck i)) := by
    filter_upwards [] with i
    have hclose := (D.sourceNeck i).metric_comparison.close
    rw [D.sourceEpsilon i] at hclose
    convert hclose using 1
    funext z v w
    simp [normalizedTensor, inv_pow]
  filter_upwards [hsource, hdiff_eventual] with i hC hd
  have hdiff : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
      cylinderJetDifferenceSquared 0 (D.targetCore i).tensor
        (normalizedTensor (D.sourceNeck i))
        ⌊eta⁻¹⌋₊ z ≤ delta := by
    intro z hz
    exact hd z hz
  have hclose : RoundCylinderClose eta 0 (D.targetCore i).tensor := by
    apply hperturb 0 (by norm_num) (D.targetCore i).tensor
      (normalizedTensor (D.sourceNeck i)) hC (D.targetCore i).tensor_smooth
    exact hdiff
  refine ⟨(D.targetCore i).toEpsilonNeck hclose, rfl, ?_, ?_⟩
  · exact D.targetCore_center i
  · exact D.targetCore_connection i

end PoincareConjecture.Proofs.M28.NeckTransfer
