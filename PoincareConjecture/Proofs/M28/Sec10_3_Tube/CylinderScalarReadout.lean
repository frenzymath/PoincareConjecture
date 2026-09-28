import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderCoordinates
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundTransfer
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.SphereGram
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Differential
import PoincareConjecture.Proofs.M13.OrdinaryFlow

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Manifold IsManifold
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds PoincareConjecture.Proofs.M28.NeckAnalysis

private abbrev CylinderReadoutE := EuclideanSpace ℝ (Fin 3)
private abbrev SphereReadoutE := EuclideanSpace ℝ (Fin 2)
private abbrev CylI := (𝓡 2).prod 𝓘(ℝ, ℝ)

def cylinderSphereParametrization (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) : RoundCylinderSpace :=
  ((chartAt SphereReadoutE q).symm p.1, p.2)

private theorem cylinderSphereParametrization_contMDiffAt
    (q : UnitTwoSphere) {p : RoundCylinderCoordinates}
    (hp : p.1 ∈ (chartAt SphereReadoutE q).target) :
    ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) CylI ∞
      (cylinderSphereParametrization q) p := by
  have hc : ContMDiffAt (𝓡 2) (𝓡 2) ∞
      (chartAt SphereReadoutE q).symm p.1 :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas q) hp
  change ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) CylI ∞
    (Prod.map (chartAt SphereReadoutE q).symm id) p
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hc.prodMap (contMDiffAt_id (I := 𝓘(ℝ, ℝ)) (x := p.2))

private theorem cylinderSphereParametrization_mfderiv
    (q : UnitTwoSphere) {p : RoundCylinderCoordinates}
    (hp : p.1 ∈ (chartAt SphereReadoutE q).target) :
    mfderiv 𝓘(ℝ, RoundCylinderCoordinates) CylI
        (cylinderSphereParametrization q) p =
      (mfderiv (𝓡 2) (𝓡 2) (chartAt SphereReadoutE q).symm p.1).prodMap
        (ContinuousLinearMap.id ℝ ℝ) := by
  have hc : ContMDiffAt (𝓡 2) (𝓡 2) ∞
      (chartAt SphereReadoutE q).symm p.1 :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas q) hp
  change mfderiv 𝓘(ℝ, RoundCylinderCoordinates) CylI
      (Prod.map (chartAt SphereReadoutE q).symm id) p = _
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
    mfderiv_prodMap (hc.mdifferentiableAt (by simp)) mdifferentiableAt_id,
    mfderiv_id]
  rfl

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

omit [IsManifold (𝓡 3) ∞ M] in

theorem contMDiffAt_cylinderMap {epsilon : ℝ} {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn CylI (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (q : UnitTwoSphere) (s : ℝ) {x : CylinderReadoutE}
    (hx : cylinderScalarCoordinates s x ∈
      (chartAt SphereReadoutE q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (f ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x := by
  have hcoords : ContMDiffAt (𝓡 3) 𝓘(ℝ, RoundCylinderCoordinates) ∞
      (cylinderScalarCoordinates s) x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiff_cylinderScalarCoordinates s).contDiffAt
  have hsphere := cylinderSphereParametrization_contMDiffAt q hx.1
  have hmap := hf.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show cylinderSphereParametrization q (cylinderScalarCoordinates s x) ∈
        univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨mem_univ _, hx.2⟩))
  exact hmap.comp x (hsphere.comp x hcoords)

omit [IsManifold (𝓡 3) ∞ M] in

theorem cylinderMap_mfderiv_apply {epsilon : ℝ} {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn CylI (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (q : UnitTwoSphere) (s : ℝ) {x : CylinderReadoutE}
    (hx : cylinderScalarCoordinates s x ∈
      (chartAt SphereReadoutE q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : CylinderReadoutE) :
    mfderiv (𝓡 3) (𝓡 3)
        (f ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x v =
      mfderiv CylI (𝓡 3) f
        (cylinderSphereParametrization q (cylinderScalarCoordinates s x))
        (mfderiv (𝓡 2) (𝓡 2) (chartAt SphereReadoutE q).symm
          (cylinderScalarCoordinates s x).1 (cylinderScalarCoordinateEquiv v).1,
          (cylinderScalarCoordinateEquiv v).2) := by
  have hcoords : ContMDiffAt (𝓡 3) 𝓘(ℝ, RoundCylinderCoordinates) ∞
      (cylinderScalarCoordinates s) x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiff_cylinderScalarCoordinates s).contDiffAt
  have hsphere := cylinderSphereParametrization_contMDiffAt q hx.1
  have hmap := hf.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show cylinderSphereParametrization q (cylinderScalarCoordinates s x) ∈
        univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨mem_univ _, hx.2⟩))
  have hcoordsDer : mfderiv (𝓡 3) 𝓘(ℝ, RoundCylinderCoordinates)
      (cylinderScalarCoordinates s) x = cylinderScalarCoordinateEquiv.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact (cylinderScalarCoordinates_hasFDerivAt s x).fderiv
  rw [mfderiv_comp x (hmap.mdifferentiableAt (by simp))
      ((hsphere.comp x hcoords).mdifferentiableAt (by simp)),
    mfderiv_comp x (hsphere.mdifferentiableAt (by simp))
      (hcoords.mdifferentiableAt (by simp)),
    hcoordsDer, cylinderSphereParametrization_mfderiv q hx.1]
  rfl

theorem cylinderMapCoefficients_eq_frozen {epsilon : ℝ}
    {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn CylI (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (Q : ℝ) (q : UnitTwoSphere) (s : ℝ) {x : CylinderReadoutE}
    (hx : cylinderScalarCoordinates s x ∈
      (chartAt SphereReadoutE q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a b : Fin 3) :
    (Q • g.pullbackCoefficients
        (f ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x)
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderTensorCoefficient
        (fun z v w => Q * roundCylinderPullback g f z v w)
        (chartAt SphereReadoutE q) (cylinderScalarCoordinates s x) a b := by
  change Q * g.inner _
      (mfderiv (𝓡 3) (𝓡 3)
        (f ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3)
        (f ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) = _
  rw [cylinderMap_mfderiv_apply hf q s hx,
    cylinderMap_mfderiv_apply hf q s hx,
    cylinderScalarCoordinateEquiv_basis, cylinderScalarCoordinateEquiv_basis]
  rfl

theorem cylinderMapCoefficients_frozen_germ {epsilon : ℝ}
    {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn CylI (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (Q : ℝ) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (a b : Fin 3) :
    (fun x => (Q • g.pullbackCoefficients
        (f ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x)
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 (0 : CylinderReadoutE)]
      (fun x => roundCylinderTensorCoefficient
        (fun z v w => Q * roundCylinderPullback g f z v w)
        (chartAt SphereReadoutE q) (cylinderScalarCoordinates s x) a b) := by
  have hopen : IsOpen ((cylinderScalarCoordinates s) ⁻¹'
      ((chartAt SphereReadoutE q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)) :=
    ((chartAt SphereReadoutE q).open_target.prod isOpen_Ioo).preimage
      (contDiff_cylinderScalarCoordinates s).continuous
  have hzero : cylinderScalarCoordinates s 0 ∈
      (chartAt SphereReadoutE q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    rw [cylinderScalarCoordinates_zero]
    refine ⟨?_, hs⟩
    rw [← sphere_chart_center q]
    exact (chartAt SphereReadoutE q).map_source (mem_chart_source _ q)
  filter_upwards [hopen.mem_nhds hzero] with x hx
  exact cylinderMapCoefficients_eq_frozen hf Q q s hx a b

theorem cylinderMapCoefficients_inverse_frozen_germ {epsilon : ℝ}
    {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn CylI (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (Q : ℝ) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (a b : Fin 3) :
    (fun p => roundCylinderTensorCoefficient
        (fun z v w => Q * roundCylinderPullback g f z v w)
        (chartAt SphereReadoutE q) p a b) =ᶠ[𝓝 (0, s)]
      (fun p => Q * g.pullbackCoefficients
        (f ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s))
        (cylinderScalarCoordinateEquiv.symm (p - (0, s)))
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) := by
  have ht : Continuous (fun p : RoundCylinderCoordinates =>
      cylinderScalarCoordinateEquiv.symm (p - (0, s))) :=
    cylinderScalarCoordinateEquiv.symm.continuous.comp (continuous_id.sub continuous_const)
  have htend : Tendsto (fun p : RoundCylinderCoordinates =>
      cylinderScalarCoordinateEquiv.symm (p - (0, s))) (𝓝 (0, s)) (𝓝 0) := by
    simpa only [sub_self, map_zero] using ht.tendsto (0, s)
  have h := (cylinderMapCoefficients_frozen_germ (g := g) hf Q q hs a b).comp_tendsto htend
  filter_upwards [h] with p hp
  simpa only [Function.comp_apply, cylinderScalarCoordinates,
    ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel,
    smul_apply, smul_eq_mul] using hp.symm

def cylinderNeckChart (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ)
    (x : CylinderReadoutE) : M :=
  N.coordinate_map (cylinderSphereParametrization q (cylinderScalarCoordinates s x))

def cylinderNeckChartDomain (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    Set CylinderReadoutE :=
  (cylinderScalarCoordinates s) ⁻¹'
    ((chartAt SphereReadoutE q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)

def cylinderNeckCoefficients (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    CylinderReadoutE → MetricCoefficient 3 :=
  fun x => N.scale⁻¹ ^ 2 • g.pullbackCoefficients (cylinderNeckChart N q s) x

theorem isOpen_cylinderNeckChartDomain (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) : IsOpen (cylinderNeckChartDomain N q s) :=
  ((chartAt SphereReadoutE q).open_target.prod isOpen_Ioo).preimage
    (contDiff_cylinderScalarCoordinates s).continuous

theorem zero_mem_cylinderNeckChartDomain (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    0 ∈ cylinderNeckChartDomain N q s := by
  change cylinderScalarCoordinates s 0 ∈
    (chartAt SphereReadoutE q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
  rw [cylinderScalarCoordinates_zero]
  refine ⟨?_, hs⟩
  rw [← sphere_chart_center q]
  exact (chartAt SphereReadoutE q).map_source (mem_chart_source _ q)

theorem cylinderNeckChart_zero (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    cylinderNeckChart N q s 0 = N.coordinate_map (q, s) := by
  have hc : (chartAt SphereReadoutE q).symm 0 = q := by
    rw [← sphere_chart_center q]
    exact (chartAt SphereReadoutE q).left_inv (mem_chart_source _ q)
  simp only [cylinderNeckChart, cylinderScalarCoordinates_zero,
    cylinderSphereParametrization, hc]

private theorem neck_coordinate_mfderiv_injective (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Function.Injective (mfderiv CylI (𝓡 3) N.coordinate_map z) := by
  have hmap := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)
  have hinv := N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds (N.coordinate_map_mem_of_axial z hz))
  have hleft : (N.coordinate_inverse ∘ N.coordinate_map) =ᶠ[𝓝 z]
      (id : RoundCylinderSpace → RoundCylinderSpace) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩]
      with y hy
    exact N.coordinate_inverse_coordinate_map_of_axial y hy.2
  have hcomp := mfderiv_comp z (hinv.mdifferentiableAt (by simp))
    (hmap.mdifferentiableAt (by simp))
  rw [hleft.mfderiv_eq, mfderiv_id] at hcomp
  intro v w hvw
  have hv := congrArg (fun L : RoundCylinderTangent z →L[ℝ]
      RoundCylinderTangent z => L v) hcomp
  have hw := congrArg (fun L : RoundCylinderTangent z →L[ℝ]
      RoundCylinderTangent z => L w) hcomp
  exact hv.trans ((congrArg
    (mfderiv (𝓡 3) CylI N.coordinate_inverse (N.coordinate_map z)) hvw).trans hw.symm)

theorem contMDiffOn_cylinderNeckChart (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderNeckChart N q s)
      (cylinderNeckChartDomain N q s) := by
  intro x hx
  have hp : cylinderScalarCoordinates s x ∈
      (chartAt SphereReadoutE q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := hx
  have hcoords : ContMDiffAt (𝓡 3) 𝓘(ℝ, RoundCylinderCoordinates) ∞
      (cylinderScalarCoordinates s) x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiff_cylinderScalarCoordinates s).contDiffAt
  have hsphere := cylinderSphereParametrization_contMDiffAt q hp.1
  have hmap := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show cylinderSphereParametrization q (cylinderScalarCoordinates s x) ∈
        univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, hp.2⟩))
  exact (hmap.comp x (hsphere.comp x hcoords)).contMDiffWithinAt

theorem cylinderNeckChart_mfderiv_apply (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : CylinderReadoutE}
    (hx : x ∈ cylinderNeckChartDomain N q s) (v : CylinderReadoutE) :
    mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x v =
      mfderiv CylI (𝓡 3) N.coordinate_map
        (cylinderSphereParametrization q (cylinderScalarCoordinates s x))
        (mfderiv (𝓡 2) (𝓡 2) (chartAt SphereReadoutE q).symm
          (cylinderScalarCoordinates s x).1 (cylinderScalarCoordinateEquiv v).1,
          (cylinderScalarCoordinateEquiv v).2) := by
  have hp : cylinderScalarCoordinates s x ∈
      (chartAt SphereReadoutE q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := hx
  have hcoords : ContMDiffAt (𝓡 3) 𝓘(ℝ, RoundCylinderCoordinates) ∞
      (cylinderScalarCoordinates s) x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiff_cylinderScalarCoordinates s).contDiffAt
  have hsphere := cylinderSphereParametrization_contMDiffAt q hp.1
  have hmap := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show cylinderSphereParametrization q (cylinderScalarCoordinates s x) ∈
        univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, hp.2⟩))
  have hcoordsDer : mfderiv (𝓡 3) 𝓘(ℝ, RoundCylinderCoordinates)
      (cylinderScalarCoordinates s) x = cylinderScalarCoordinateEquiv.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact (cylinderScalarCoordinates_hasFDerivAt s x).fderiv
  change mfderiv (𝓡 3) (𝓡 3)
    (N.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x v = _
  rw [mfderiv_comp x (hmap.mdifferentiableAt (by simp))
      ((hsphere.comp x hcoords).mdifferentiableAt (by simp)),
    mfderiv_comp x (hsphere.mdifferentiableAt (by simp))
      (hcoords.mdifferentiableAt (by simp)),
    hcoordsDer, cylinderSphereParametrization_mfderiv q hp.1]
  rfl

theorem cylinderNeckChart_mfderiv_isInvertible (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : CylinderReadoutE}
    (hx : x ∈ cylinderNeckChartDomain N q s) :
    (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x).IsInvertible := by
  have hp : cylinderScalarCoordinates s x ∈
      (chartAt SphereReadoutE q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := hx
  have hc : Function.Injective (mfderiv (𝓡 2) (𝓡 2)
      (chartAt SphereReadoutE q).symm (cylinderScalarCoordinates s x).1) :=
    (mdifferentiable_chart (I := 𝓡 2) q).symm.mfderiv_injective hp.1
  apply RiemannianMetric.isInvertible_mfderiv_of_injective
  intro v w hvw
  rw [cylinderNeckChart_mfderiv_apply N q s hx,
    cylinderNeckChart_mfderiv_apply N q s hx] at hvw
  have hpair := (neck_coordinate_mfderiv_injective N
    (z := cylinderSphereParametrization q (cylinderScalarCoordinates s x)) hp.2) hvw
  apply cylinderScalarCoordinateEquiv.injective
  apply Prod.ext
  · exact hc (congrArg Prod.fst hpair)
  · simpa only using congrArg Prod.snd hpair

theorem contDiffOn_cylinderNeckCoefficients (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) :
    ContDiffOn ℝ ∞ (cylinderNeckCoefficients N q s)
      (cylinderNeckChartDomain N q s) := by
  intro x hx
  have hchart := (contMDiffOn_cylinderNeckChart N q s).contMDiffAt
    ((isOpen_cylinderNeckChartDomain N q s).mem_nhds hx)
  exact ((g.contDiffAt_pullbackCoefficients hchart).const_smul
    (N.scale⁻¹ ^ 2)).contDiffWithinAt

theorem cylinderNeckCoefficients_eq_frozen (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : CylinderReadoutE}
    (hx : x ∈ cylinderNeckChartDomain N q s) (a b : Fin 3) :
    cylinderNeckCoefficients N q s x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderTensorCoefficient
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
        (chartAt SphereReadoutE q) (cylinderScalarCoordinates s x) a b := by
  change N.scale⁻¹ ^ 2 * g.inner (cylinderNeckChart N q s x)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) = _
  rw [cylinderNeckChart_mfderiv_apply N q s hx,
    cylinderNeckChart_mfderiv_apply N q s hx,
    cylinderScalarCoordinateEquiv_basis, cylinderScalarCoordinateEquiv_basis]
  rfl

theorem cylinderNeckCoefficients_frozen_germ (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (a b : Fin 3) :
    (fun x => cylinderNeckCoefficients N q s x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 (0 : CylinderReadoutE)]
      (fun x => roundCylinderTensorCoefficient
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
        (chartAt SphereReadoutE q) (cylinderScalarCoordinates s x) a b) := by
  filter_upwards [(isOpen_cylinderNeckChartDomain N q s).mem_nhds
    (zero_mem_cylinderNeckChartDomain N q hs)] with x hx
  exact cylinderNeckCoefficients_eq_frozen N q s hx a b

theorem cylinderNeckCoefficients_scalar_eq [T2Space M]
    (N : EpsilonNeck g) (D : LeviCivitaData g)
    (q : UnitTwoSphere) (s : ℝ) {x : CylinderReadoutE}
    (hx : x ∈ cylinderNeckChartDomain N q s) :
    jetScalarCurvature (metricTwoJet (cylinderNeckCoefficients N q s) x) =
      N.scale ^ 2 * D.scalarCurvature (cylinderNeckChart N q s x) := by
  let Q : ℝ := N.scale⁻¹ ^ 2
  have hQ : 0 < Q := pow_pos (inv_pos.mpr N.scale_pos) 2
  let gs : RiemannianMetric 3 M := M13.scaleSmoothMetric g Q hQ
  let Ds : LeviCivitaData gs := M13.scaleLeviCivitaData D Q hQ
  have hcoeff : cylinderNeckCoefficients N q s =
      gs.pullbackCoefficients (cylinderNeckChart N q s) := by
    funext y
    ext v w
    rfl
  rw [hcoeff, jetScalarCurvature_metricTwoJet_pullback Ds
    (isOpen_cylinderNeckChartDomain N q s)
    (contMDiffOn_cylinderNeckChart N q s)
    (fun _ hy => cylinderNeckChart_mfderiv_isInvertible N q s hy) hx]
  have hscale := M13.homothety_scalarCurvature_eq g gs
    (Diffeomorph.refl (𝓡 3) M ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) D Ds (cylinderNeckChart N q s x)
  simp only [Diffeomorph.coe_refl, id_eq] at hscale
  rw [hscale]
  simp only [Q, div_eq_mul_inv, inv_pow, inv_inv, mul_comm]

theorem cylinderNeckCoefficients_scalar_zero [T2Space M]
    (N : EpsilonNeck g) (D : LeviCivitaData g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    jetScalarCurvature (metricTwoJet (cylinderNeckCoefficients N q s) 0) =
      N.scale ^ 2 * D.scalarCurvature (N.coordinate_map (q, s)) := by
  rw [cylinderNeckCoefficients_scalar_eq N D q s
    (zero_mem_cylinderNeckChartDomain N q hs), cylinderNeckChart_zero]

end PoincareConjecture.M28.tube
