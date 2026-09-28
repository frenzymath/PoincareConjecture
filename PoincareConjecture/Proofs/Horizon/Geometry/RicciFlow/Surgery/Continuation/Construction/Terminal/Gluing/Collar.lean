import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Retention
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.OpenSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Neck.NeckCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}

namespace MetricSurgeryInput

def sourceCarrier (_I : MetricSurgeryInput K g) : GeneralizedSliceCarrier.{u} where
  carrier := M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

def retainedCollar (I : MetricSurgeryInput K g) : Opens M :=
  ⟨I.neck.region (-I.neck.epsilon⁻¹) 1, MetricSurgery.neck_region_isOpen _ _ _⟩

def negativeHalf (I : MetricSurgeryInput K g) : Opens M :=
  ⟨I.neck.region (-I.neck.epsilon⁻¹) 0, MetricSurgery.neck_region_isOpen _ _ _⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem negativeHalf_subset_retainedCollar (I : MetricSurgeryInput K g) :
    (I.negativeHalf : Set M) ⊆ I.retainedCollar := by
  intro x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.trans (by norm_num)⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem centralSphere_subset_retainedCollar (I : MetricSurgeryInput K g) :
    I.neck.central_sphere ⊆ I.retainedCollar := by
  intro x hx
  obtain ⟨hxN, hx0⟩ := (MetricSurgery.neck_central_iff I.neck).mp hx
  exact ⟨hxN, by rw [hx0]; linarith [inv_pos.mpr I.neck.epsilon_pos], by rw [hx0]; norm_num⟩

end MetricSurgeryInput

namespace MetricSurgeryResult

variable {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

def retainedRegionEquivalence (U : Set M) (hU : U ⊆ I.retainedCollar) :
    SurgeryRegionEquivalence I.sourceCarrier R.output U (R.collapse '' U) where
  map := R.collapse
  inverse := R.retained_inverse
  map_image := rfl
  inverse_image := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [R.retained_left_inverse (hU hz)] using hz
    · intro hx
      exact ⟨R.collapse x, mem_image_of_mem _ hx, R.retained_left_inverse (hU hx)⟩
  left_inverse := R.retained_left_inverse.mono hU
  right_inverse := R.retained_right_inverse.mono (image_subset_range _ _)
  map_smooth := R.retained_smooth.mono hU
  inverse_smooth := R.retained_inverse_smooth.mono (image_mono hU)

theorem retained_image_isOpen (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar) :
    IsOpen (R.collapse '' (U : Set M)) :=
  (R.retainedRegionEquivalence U hU).image_isOpen U.isOpen
    (by rw [U.isOpen.interior_eq])

def retainedImage (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar) :
    Opens R.output.carrier := ⟨R.collapse '' (U : Set M), R.retained_image_isOpen U hU⟩

def retainedDiffeomorph (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar) :
    Diffeomorph (𝓡 3) (𝓡 3) U (R.retainedImage U hU) ∞ where
  toFun x := ⟨R.collapse x.val, mem_image_of_mem _ x.property⟩
  invFun y := ⟨R.retained_inverse y.val, by
    obtain ⟨x, hx, hxy⟩ := y.property
    rw [← hxy, R.retained_left_inverse (hU hx)]
    exact hx⟩
  left_inv x := Subtype.ext (R.retained_left_inverse (hU x.property))
  right_inv y := Subtype.ext (R.retained_right_inverse (image_subset_range _ _ y.property))
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (R.retainedImage U hU) _).mp
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact ((R.retained_smooth.mono hU) x x.property).contMDiffAt (U.isOpen.mem_nhds x.property)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    intro y
    apply contMDiffAt_subtype_iff.mpr
    exact (R.retained_inverse_smooth y ((image_mono hU) y.property)).contMDiffAt
      (Filter.mem_of_superset ((R.retainedImage U hU).isOpen.mem_nhds y.property) (image_mono hU))

@[simp] theorem retainedDiffeomorph_apply (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar)
    (x : U) : (R.retainedDiffeomorph U hU x).val = R.collapse x.val := rfl

@[simp] theorem retainedDiffeomorph_symm_apply (U : Opens M)
    (hU : (U : Set M) ⊆ I.retainedCollar) (y : R.retainedImage U hU) :
    ((R.retainedDiffeomorph U hU).symm y).val = R.retained_inverse y.val := rfl

def retainedMap (U : Opens M) (_hU : (U : Set M) ⊆ I.retainedCollar) :
    U → R.output.carrier := fun x => R.collapse x.val

theorem retainedMap_smooth (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (R.retainedMap U hU) :=
  contMDiff_subtype_val.comp (R.retainedDiffeomorph U hU).contMDiff

theorem retainedMap_openEmbedding (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar) :
    Topology.IsOpenEmbedding (R.retainedMap U hU) :=
  (R.retainedImage U hU).isOpen.isOpenEmbedding_subtypeVal.comp
    (R.retainedDiffeomorph U hU).toHomeomorph.isOpenEmbedding

theorem retainedMap_isLocalDiffeomorph (U : Opens M)
    (hU : (U : Set M) ⊆ I.retainedCollar) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (R.retainedMap U hU) := by
  intro x
  exact ((R.retainedDiffeomorph U hU).isLocalDiffeomorph x).comp (𝓡 3) R.output.carrier
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (R.retainedImage U hU) _)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem retainedMap_left_inverse (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar)
    (x : U) : R.retained_inverse (R.retainedMap U hU x) = x.val :=
  R.retained_left_inverse (hU x.property)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem retainedMap_range (U : Opens M) (hU : (U : Set M) ⊆ I.retainedCollar) :
    range (R.retainedMap U hU) = R.collapse '' (U : Set M) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_image_of_mem _ x.property
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

abbrev collarDiffeomorph := R.retainedDiffeomorph I.retainedCollar subset_rfl

abbrev negativeDiffeomorph :=
  R.retainedDiffeomorph I.negativeHalf I.negativeHalf_subset_retainedCollar

def negativeMap : I.negativeHalf → R.output.carrier :=
  R.retainedMap I.negativeHalf I.negativeHalf_subset_retainedCollar

theorem negativeMap_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ R.negativeMap :=
  R.retainedMap_smooth I.negativeHalf I.negativeHalf_subset_retainedCollar

theorem negativeMap_openEmbedding : Topology.IsOpenEmbedding R.negativeMap :=
  R.retainedMap_openEmbedding I.negativeHalf I.negativeHalf_subset_retainedCollar

theorem negativeMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ R.negativeMap :=
  R.retainedMap_isLocalDiffeomorph I.negativeHalf I.negativeHalf_subset_retainedCollar

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem negativeMap_left_inverse (x : I.negativeHalf) :
    R.retained_inverse (R.negativeMap x) = x.val :=
  R.retainedMap_left_inverse I.negativeHalf I.negativeHalf_subset_retainedCollar x

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem negativeMap_range : range R.negativeMap = R.collapse '' (I.negativeHalf : Set M) :=
  R.retainedMap_range I.negativeHalf I.negativeHalf_subset_retainedCollar

theorem negativeMap_metric (x : I.negativeHalf) (v w : TangentSpace (𝓡 3) x) :
    R.metric.inner (R.negativeMap x)
      (mfderiv (𝓡 3) (𝓡 3) R.negativeMap x v)
      (mfderiv (𝓡 3) (𝓡 3) R.negativeMap x w) =
        (I.sourceCarrier.openSubsetMetric I.negativeHalf g).inner x v w := by
  have hder (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) R.negativeMap x z =
        mfderiv (𝓡 3) (𝓡 3) R.collapse x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : I.negativeHalf → M) x z) :=
    mfderiv_comp_apply x
      (((R.retained_smooth x (I.negativeHalf_subset_retainedCollar x.property)).contMDiffAt
        (I.retainedCollar.isOpen.mem_nhds
          (I.negativeHalf_subset_retainedCollar x.property))).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x) z
  rw [hder v, hder w]
  exact R.retained_metric x (Or.inl x.property) _ _

theorem negativeMap_pullback_metric :
    R.metric.pullbackOfLocalDiffeomorph R.negativeMap R.negativeMap_isLocalDiffeomorph =
      I.sourceCarrier.openSubsetMetric I.negativeHalf g := by
  have hinner :
      (R.metric.pullbackOfLocalDiffeomorph R.negativeMap
        R.negativeMap_isLocalDiffeomorph).inner =
          (I.sourceCarrier.openSubsetMetric I.negativeHalf g).inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact R.negativeMap_metric x v w
  have hext : ∀ g₁ g₂ : RiemannianMetric 3 I.negativeHalf,
      g₁.inner = g₂.inner → g₁ = g₂ := by
    rintro ⟨inner₁, _, _, _, _⟩ ⟨inner₂, _, _, _, _⟩ heq
    cases heq
    rfl
  exact hext _ _ hinner

theorem retained_inverse_contMDiffAt_central {x : M} (hx : x ∈ I.neck.central_sphere) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ R.retained_inverse (R.collapse x) :=
  (R.retained_inverse_smooth _
    (mem_image_of_mem _ (I.centralSphere_subset_retainedCollar hx))).contMDiffAt
      ((R.retained_image_isOpen I.retainedCollar subset_rfl).mem_nhds
        (mem_image_of_mem _ (I.centralSphere_subset_retainedCollar hx)))

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem retained_inverse_central {x : M} (hx : x ∈ I.neck.central_sphere) :
    R.retained_inverse (R.collapse x) = x :=
  R.retained_left_inverse (I.centralSphere_subset_retainedCollar hx)

end MetricSurgeryResult

end PoincareConjecture
