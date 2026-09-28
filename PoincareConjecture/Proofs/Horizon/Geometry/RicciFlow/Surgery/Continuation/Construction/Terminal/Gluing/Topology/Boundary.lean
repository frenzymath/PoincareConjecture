import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.CapChart








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

namespace EpsilonNeck

def centralSphereHomeomorph (N : EpsilonNeck g) : UnitTwoSphere ≃ₜ N.central_sphere where
  toFun θ := ⟨N.coordinate_map (θ, 0), by
    rw [N.central_sphere_eq]
    exact mem_image_of_mem _ ⟨mem_univ _, rfl⟩⟩
  invFun x := (N.coordinate_inverse x.val).1
  left_inv θ := congrArg Prod.fst (MetricSurgery.neck_inverse_coordinate N (θ, 0)
    ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩)
  right_inv x := by
    apply Subtype.ext
    have hx := (MetricSurgery.neck_central_iff N).mp x.property
    simpa only [← hx.2, Prod.mk.eta] using MetricSurgery.neck_coordinate_inverse N hx.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact N.coordinate_map_smooth.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun θ =>
        ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩)
  continuous_invFun :=
    (N.coordinate_inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
      (fun x => N.central_sphere_subset x.property)).fst

@[simp] theorem centralSphereHomeomorph_apply (N : EpsilonNeck g) (θ : UnitTwoSphere) :
    (N.centralSphereHomeomorph θ).val = N.coordinate_map (θ, 0) := rfl

@[simp] theorem centralSphereHomeomorph_symm_apply (N : EpsilonNeck g)
    (x : N.central_sphere) : N.centralSphereHomeomorph.symm x = (N.coordinate_inverse x.val).1 := rfl

end EpsilonNeck

namespace MetricSurgeryResult

variable {K : MetricSurgeryConstants} {g₀ : StandardInitialMetric}
  {I : MetricSurgeryInput K g} (R : MetricSurgeryResult g₀ I)

def capBoundaryToCentral (x : Metric.sphere (0 : StandardCapSpace) R.capEuclideanRadius) :
    I.neck.central_sphere :=
  ⟨R.retained_inverse (R.cap_map x.val), by
    obtain ⟨y, hy, he⟩ := R.capEuclidean_sphere_image.subset (mem_image_of_mem _ x.property)
    rw [← he, R.retained_left_inverse (I.centralSphere_subset_retainedCollar hy)]
    exact hy⟩

theorem collapse_capBoundaryToCentral
    (x : Metric.sphere (0 : StandardCapSpace) R.capEuclideanRadius) :
    R.collapse (R.capBoundaryToCentral x).val = R.cap_map x.val := by
  apply R.retained_right_inverse
  exact image_subset_range _ _
    (R.capEuclidean_sphere_image.subset (mem_image_of_mem _ x.property))

theorem capBoundaryToCentral_bijective : Function.Bijective R.capBoundaryToCentral := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply R.cap_left_inverse.injOn
      (R.capEuclidean_closedBall_subset (Metric.sphere_subset_closedBall x.property))
      (R.capEuclidean_closedBall_subset (Metric.sphere_subset_closedBall y.property))
    exact (R.collapse_capBoundaryToCentral x).symm.trans
      ((congrArg (fun p : I.neck.central_sphere => R.collapse p.val) hxy).trans
        (R.collapse_capBoundaryToCentral y))
  · intro y
    obtain ⟨x, hx, hxy⟩ := R.capEuclidean_sphere_image.superset
      (mem_image_of_mem _ y.property)
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change R.retained_inverse (R.cap_map x) = y.val
    rw [hxy]
    exact R.retained_left_inverse (I.centralSphere_subset_retainedCollar y.property)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]

theorem capBoundaryToCentral_continuous : Continuous R.capBoundaryToCentral := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx := (R.capBoundaryToCentral x).property
  have hy := I.centralSphere_subset_retainedCollar hx
  have he := R.collapse_capBoundaryToCentral x
  have hy' : R.cap_map x.val ∈ R.collapse '' (I.retainedCollar : Set M) :=
    he ▸ mem_image_of_mem _ hy
  have hi := (R.retained_inverse_smooth _ hy').contMDiffAt
    ((R.retained_image_isOpen I.retainedCollar subset_rfl).mem_nhds hy')
  exact hi.continuousAt.comp
    (f := fun z : Metric.sphere (0 : StandardCapSpace) R.capEuclideanRadius => R.cap_map z.val)
    ((R.cap_map_smooth.continuousOn.comp_continuous
      (continuous_subtype_val (p := fun z : StandardCapSpace =>
        z ∈ Metric.sphere 0 R.capEuclideanRadius))
      (fun z => R.capEuclidean_closedBall_subset
        (Metric.sphere_subset_closedBall z.property))).continuousAt)

def capBoundaryHomeomorph :
    Metric.sphere (0 : StandardCapSpace) R.capEuclideanRadius ≃ₜ I.neck.central_sphere := by
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective R.capBoundaryToCentral R.capBoundaryToCentral_bijective)
    R.capBoundaryToCentral_continuous

def capBoundaryAngles :
    Metric.sphere (0 : StandardCapSpace) R.capEuclideanRadius ≃ₜ UnitTwoSphere :=
  R.capBoundaryHomeomorph.trans I.neck.centralSphereHomeomorph.symm

theorem coordinate_capBoundaryAngles
    (x : Metric.sphere (0 : StandardCapSpace) R.capEuclideanRadius) :
    I.neck.coordinate_map (R.capBoundaryAngles x, 0) = R.retained_inverse (R.cap_map x.val) := by
  have h := I.neck.centralSphereHomeomorph.apply_symm_apply (R.capBoundaryHomeomorph x)
  exact congrArg Subtype.val h

end MetricSurgeryResult
end PoincareConjecture
