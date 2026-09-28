import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceNeck
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCurvatureReadout










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.SpacetimeBounds tube

private abbrev CE := EuclideanSpace ℝ (Fin 3)
private abbrev CylI := (𝓡 2).prod 𝓘(ℝ, ℝ)

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))



theorem GeneralizedStrongNeck.rescaled_metric_at_time
    (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) (x : strongNeckOpen S)
    (v w : TangentSpace (𝓡 3) x) :
    (H.rescaling.flow.metric s).inner x v w =
      S.time_cylinder.pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          x w) := by
  let K := Proofs.M12.cylinderPhysicalInterval t (S.scale⁻¹ ^ 2)
    S.time_cylinder.scale_pos strongNeckBackwardInterval
  have hP : s ∈
      (parabolicInterval (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos t K).domain := by
    apply (mem_parabolicInterval_iff (S.scale⁻¹ ^ 2) S.time_cylinder.scale_pos t K s).2
    exact ⟨s, hs, rfl⟩
  have hm := rescaled_pullback_metric_eq
    (e := strongNeckCylinder S) (hI := GeneralizedStrongNeck.physical_interval_subset S)
    H ⟨s, hP⟩ x v w
  have hm' : (H.rescaling.flow.metric s).inner x v w =
      (strongNeckCylinder S).pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          x w) := by
    simpa only [rescaledTime_val] using hm
  have hforward : (strongNeckCylinder S).forward s hs = S.time_cylinder.forward s hs := by
    funext y
    simp [strongNeckCylinder]
  exact hm'.trans (congrArg
    (fun f : (F.slice t).carrier → (F.slice (t + s / S.scale⁻¹ ^ 2)).carrier =>
      S.scale⁻¹ ^ 2 * (F.metric (t + s / S.scale⁻¹ ^ 2)).inner (f x.val)
        (mfderiv (𝓡 3) (𝓡 3) f x.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x v))
        (mfderiv (𝓡 3) (𝓡 3) f x.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x w))) hforward)



theorem strongNeckSource_tensor_eq_on_strip_at_time
    (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback (H.rescaling.flow.metric s) (strongNeckSourceMap S) z v w =
      generalizedCylinderPullback S.time_cylinder S.coordinate_map s z v w := by
  let : ChartedSpace CE (strongNeckOpen S).carrier :=
    TopologicalSpace.Opens.instChartedSpace (strongNeckOpen S)
  have hz' : z ∈ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := ⟨mem_univ _, hz⟩
  have hstrip : univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ ∈ 𝓝 z :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds hz'
  have heq : (Subtype.val ∘ strongNeckSourceMap S) =ᶠ[𝓝 z] S.coordinate_map := by
    filter_upwards [hstrip] with y hy
    exact strongNeckSourceMap_val_on_strip S y hy.2
  have hderiv_v :
      mfderiv CylI (𝓡 3) (Subtype.val ∘ strongNeckSourceMap S) z v =
        mfderiv CylI (𝓡 3) S.coordinate_map z v := by
    exact congrArg
      (fun L : RoundCylinderTangent z →L[ℝ]
        TangentSpace (𝓡 3) ((Subtype.val ∘ strongNeckSourceMap S) z) => L v)
      (heq.mfderiv_eq (I := CylI) (I' := 𝓡 3))
  have hderiv_w :
      mfderiv CylI (𝓡 3) (Subtype.val ∘ strongNeckSourceMap S) z w =
        mfderiv CylI (𝓡 3) S.coordinate_map z w := by
    exact congrArg
      (fun L : RoundCylinderTangent z →L[ℝ]
        TangentSpace (𝓡 3) ((Subtype.val ∘ strongNeckSourceMap S) z) => L w)
      (heq.mfderiv_eq (I := CylI) (I' := 𝓡 3))
  have hf : ContMDiffAt CylI (𝓡 3) ∞ (strongNeckSourceMap S) z :=
    (strongNeckSourceMap_smooth S z hz').contMDiffAt hstrip
  have hcomp_v := mfderiv_comp_apply z
    ((contMDiff_subtype_val (U := strongNeckOpen S)
      (strongNeckSourceMap S z)).mdifferentiableAt (n := ∞) (by simp))
    (hf.mdifferentiableAt (n := ∞) (by simp)) v
  have hcomp_w := mfderiv_comp_apply z
    ((contMDiff_subtype_val (U := strongNeckOpen S)
      (strongNeckSourceMap S z)).mdifferentiableAt (n := ∞) (by simp))
    (hf.mdifferentiableAt (n := ∞) (by simp)) w
  have hm := GeneralizedStrongNeck.rescaled_metric_at_time S H s hs
    (strongNeckSourceMap S z)
    (mfderiv CylI (𝓡 3) (strongNeckSourceMap S) z v)
    (mfderiv CylI (𝓡 3) (strongNeckSourceMap S) z w)
  change (H.rescaling.flow.metric s).inner (strongNeckSourceMap S z)
      (mfderiv CylI (𝓡 3) (strongNeckSourceMap S) z v)
      (mfderiv CylI (𝓡 3) (strongNeckSourceMap S) z w) = _
  calc
    _ = S.time_cylinder.pullbackInner s hs (strongNeckSourceMap S z).val
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          (strongNeckSourceMap S z)
          (mfderiv CylI (𝓡 3) (strongNeckSourceMap S) z v))
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          (strongNeckSourceMap S z)
          (mfderiv CylI (𝓡 3) (strongNeckSourceMap S) z w)) := hm
    _ = S.time_cylinder.pullbackInner s hs (strongNeckSourceMap S z).val
        (mfderiv CylI (𝓡 3) (Subtype.val ∘ strongNeckSourceMap S) z v)
        (mfderiv CylI (𝓡 3) (Subtype.val ∘ strongNeckSourceMap S) z w) := by
      rw [← hcomp_v, ← hcomp_w]
      rfl
    _ = S.time_cylinder.pullbackInner s hs (S.coordinate_map z)
        (mfderiv CylI (𝓡 3) S.coordinate_map z v)
        (mfderiv CylI (𝓡 3) S.coordinate_map z w) := by
      rw [hderiv_v, hderiv_w, strongNeckSourceMap_val_on_strip S z hz]
    _ = generalizedCylinderPullback S.time_cylinder S.coordinate_map s z v w := by
      simp only [generalizedCylinderPullback, dif_pos hs]



theorem GeneralizedStrongNeck.rescaled_source_comparison
    (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
    RoundCylinderClose epsilon s
      (roundCylinderPullback (H.rescaling.flow.metric s) (strongNeckSourceMap S)) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := S.metric_comparison
  apply cylinderClose_of_eqOn_strip ⟨hsmooth s hs, bound, hbound, hjet s hs⟩
  intro z hz v w
  exact (strongNeckSource_tensor_eq_on_strip_at_time S H s hs z hz v w).symm



def strongNeckCurvatureCoefficients (hepsilon : epsilon < 1 / 2)
    (s : ℝ) (q : UnitTwoSphere) (a : ℝ) : CE → MetricCoefficient 3 :=
  (H.rescaling.flow.metric s).pullbackCoefficients
    (cylinderNeckChart (GeneralizedStrongNeck.rescaled_source_neck S hepsilon H) q a)



theorem strongNeckCurvatureCoefficients_contDiffAt (hepsilon : epsilon < 1 / 2)
    (s : ℝ) (q : UnitTwoSphere) {a : ℝ} (ha : a ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContDiffAt ℝ ∞ (strongNeckCurvatureCoefficients S H hepsilon s q a) 0 := by
  let N := GeneralizedStrongNeck.rescaled_source_neck S hepsilon H
  exact (H.rescaling.flow.metric s).contDiffAt_pullbackCoefficients
    ((contMDiffOn_cylinderNeckChart N q a).contMDiffAt
      ((isOpen_cylinderNeckChartDomain N q a).mem_nhds
        (zero_mem_cylinderNeckChartDomain N q ha)))



theorem strongNeckCurvatureCoefficients_frozen_germ (hepsilon : epsilon < 1 / 2)
    (s : ℝ) (q : UnitTwoSphere) {a : ℝ} (ha : a ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (i j : Fin 3) :
    (fun x => strongNeckCurvatureCoefficients S H hepsilon s q a x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
      =ᶠ[𝓝 (0 : CE)]
      (fun x => roundCylinderTensorCoefficient
        (roundCylinderPullback (H.rescaling.flow.metric s) (strongNeckSourceMap S))
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (cylinderScalarCoordinates a x) i j) := by
  let N := GeneralizedStrongNeck.rescaled_source_neck S hepsilon H
  filter_upwards [(isOpen_cylinderNeckChartDomain N q a).mem_nhds
    (zero_mem_cylinderNeckChartDomain N q ha)] with x hx
  change (H.rescaling.flow.metric s).inner (cylinderNeckChart N q a x)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q a) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q a) x
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [cylinderNeckChart_mfderiv_apply N q a hx,
    cylinderNeckChart_mfderiv_apply N q a hx,
    cylinderScalarCoordinateEquiv_basis, cylinderScalarCoordinateEquiv_basis]
  rfl



theorem strongNeckCurvatureCoefficients_norm_zero (hepsilon : epsilon < 1 / 2)
    (s : ℝ) (q : UnitTwoSphere) {a : ℝ} (ha : a ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    jetCurvatureNorm (metricTwoJet (strongNeckCurvatureCoefficients S H hepsilon s q a) 0) =
      (H.rescaling.flow.connection s).curvatureTensorNorm (strongNeckSourceMap S (q, a)) := by
  let N := GeneralizedStrongNeck.rescaled_source_neck S hepsilon H
  change jetCurvatureNorm (metricTwoJet
    ((H.rescaling.flow.metric s).pullbackCoefficients (cylinderNeckChart N q a)) 0) = _
  rw [jetCurvatureNorm_metricTwoJet_pullback (H.rescaling.flow.connection s)
    (isOpen_cylinderNeckChartDomain N q a) (contMDiffOn_cylinderNeckChart N q a)
    (fun _ hx => cylinderNeckChart_mfderiv_isInvertible N q a hx)
    (zero_mem_cylinderNeckChartDomain N q ha), cylinderNeckChart_zero]
  rfl

end PoincareConjecture.M28
