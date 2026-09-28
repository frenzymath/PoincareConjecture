import PoincareConjecture.Proofs.M47.CanonicalNeckPushedCylinder
import PoincareConjecture.Proofs.M47.CanonicalNeckIsometricImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_physical_strong_neck_of_family
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}} {origin : ℝ}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    (e : SurgeryFlowCylinder F C origin (N.scale⁻¹ ^ 2)
      (Ioc (-1 : ℝ) 0) N.carrier)
    (hscalar : (F.connection (origin + 0 / (N.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) N.center) =
        N.connection.scalarCurvature N.center)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e N.coordinate_map)) :
    ∃ S : SurgeryStrongNeck F (origin + 0 / (N.scale⁻¹ ^ 2)) N.epsilon,
      S.neck.center = e.forward 0 (by constructor <;> norm_num) N.center := by
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  let chart := M44.cylinderSliceChart e N.carrier_open 0 hzero
  let ep := chart.toOpenPartialHomeomorph
  have hep : (ep : C.carrier → (F.slice (origin + 0 / (N.scale⁻¹ ^ 2))).carrier) =
      e.forward 0 hzero := rfl
  have hclose0 : RoundCylinderClose N.epsilon 0
      (surgeryCylinderPullback e N.coordinate_map 0) :=
    ⟨hfamily.1 0 hzero, hfamily.2.choose, hfamily.2.choose_spec.1,
      hfamily.2.choose_spec.2 0 hzero⟩
  have hclose : RoundCylinderClose N.epsilon 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback (F.metric (origin + 0 / (N.scale⁻¹ ^ 2)))
        (e.forward 0 hzero ∘ N.coordinate_map) z v w) := by
    apply hclose0.congr_cylinder
    intro z hz v w
    have hzN : N.coordinate_map z ∈ N.carrier :=
      N.coordinatePartialDiffeomorph.map_source ⟨mem_univ _, hz⟩
    have hNd := (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
    have hed := ((e.forward_smooth 0 hzero).contMDiffAt
      (N.carrier_open.mem_nhds hzN)).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp z hed hNd
    simp only [surgeryCylinderPullback, dif_pos hzero, SurgeryFlowCylinder.pullbackInner,
      roundCylinderPullback, Function.comp_apply, hchain, ContinuousLinearMap.comp_apply]
  have hc : N.center ∈ N.coordinate_map '' (univ ×ˢ ({0} : Set ℝ)) := by
    rw [← N.central_sphere_eq]
    exact N.center_on_central_sphere
  obtain ⟨⟨q, s⟩, ⟨_hq, hs⟩, hpoint⟩ := hc
  have hs0 : s = 0 := hs
  subst s
  have hdom : Ioo (-N.epsilon⁻¹ + (0 : ℝ)) (N.epsilon⁻¹ + 0) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by simp only [add_zero, Subset.rfl]
  have hregion : N.region (-N.epsilon⁻¹ + (0 : ℝ)) (N.epsilon⁻¹ + 0) ⊆ ep.source :=
    fun _ hx => hx.1
  let D := F.connection (origin + 0 / (N.scale⁻¹ ^ 2))
  have hpositive : 0 < D.scalarCurvature (ep (N.coordinate_map (q, 0))) := by
    change 0 < (F.connection (origin + 0 / (N.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 hzero (N.coordinate_map (q, 0)))
    rw [hpoint, hscalar]
    exact N.scalar_center_pos
  have hscale : N.scale = D.scalarCurvature (ep (N.coordinate_map (q, 0))) ^
      (-1 / 2 : ℝ) := by
    change N.scale = (F.connection (origin + 0 / (N.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 hzero (N.coordinate_map (q, 0))) ^ (-1 / 2 : ℝ)
    rw [hpoint, hscalar]
    exact N.scale_eq_scalar
  have hclose' : RoundCylinderClose N.epsilon 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback (F.metric (origin + 0 / (N.scale⁻¹ ^ 2)))
        (fun z => ep (N.coordinate_map (z.1, z.2 + 0))) z v w) := by
    simpa only [hep, add_zero, Prod.mk.eta, Function.comp_def] using hclose
  let N' := N.imageShift ep chart.contMDiffOn chart.symm.contMDiffOn
    N.epsilon_pos N.epsilon_lt_half hdom hregion D q N.scale_pos hpositive hscale hclose'
  have hsets := N.imageShift_zero_sets ep chart.contMDiffOn chart.symm.contMDiffOn
    N.epsilon_pos N.epsilon_lt_half hdom hregion D q N.scale_pos hpositive hscale hclose' rfl rfl
  have hcarrier : N'.carrier ⊆ e.forward 0 hzero '' N.carrier := by
    change (N.imageShift ep chart.contMDiffOn chart.symm.contMDiffOn
      N.epsilon_pos N.epsilon_lt_half hdom hregion D q N.scale_pos hpositive hscale hclose').carrier
        ⊆ e.forward 0 hzero '' N.carrier
    rw [hsets.1, hep]
  have hcoordinate : N'.coordinate_map = e.forward 0 hzero ∘ N.coordinate_map := by
    funext z
    change ep (N.coordinate_map (z.1, z.2 + 0)) =
      (e.forward 0 hzero ∘ N.coordinate_map) z
    simp only [hep, add_zero, Prod.mk.eta, Function.comp_apply]
  let pushed := neckPushedCylinder e N.carrier_open hzero N.carrier (Subset.refl N.carrier)
  let d : SurgeryFlowCylinder F (F.slice (origin + 0 / (N.scale⁻¹ ^ 2)))
      (origin + 0 / (N.scale⁻¹ ^ 2)) (N'.scale⁻¹ ^ 2) (Ioc (-1 : ℝ) 0) N'.carrier :=
    pushed.restrict (Subset.refl _) ordConnected_Ioc hcarrier
  have hcomparison : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback d N'.coordinate_map) := by
    apply hfamily.congr_cylinder
    intro s hs z hz v w
    rw [hcoordinate]
    have hNd := (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
    have hzN : N.coordinate_map z ∈ N.carrier :=
      N.coordinatePartialDiffeomorph.map_source ⟨mem_univ _, hz⟩
    exact (neckPushedCylinder_cylinderPullback e N.carrier_open hzero N.carrier
      (Subset.refl N.carrier) s hs hNd hzN v w).symm
  refine ⟨{
    neck := N'
    epsilon_eq := rfl
    connection_eq := rfl
    cylinder := d
    terminal_identity := fun h x hx =>
      neckPushedCylinder_zero_identity e N.carrier_open hzero N.carrier
        (Subset.refl N.carrier) h x (hcarrier hx)
    metric_comparison := hcomparison }, ?_⟩
  exact congrArg (e.forward 0 hzero) hpoint

end PoincareConjecture.Proofs.M47
