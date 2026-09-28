import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_FlowJoin
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_RecentNeck
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Normalization
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_CylinderCoefficients

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45NeckGluingInput

open M36 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem piecewiseTensor_joint_smooth {epsilon beta : ℝ}
    (I : M45NeckGluingInput.{u} epsilon beta)
    (hpos : 0 < beta * epsilon) (hsmall : beta * epsilon < 1 / 2)
    (q : UnitTwoSphere) (i j : Fin 3) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient (I.piecewiseTensor I.recent_patch.coordinate p.1)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p.2 i j)
      (Ioc (-I.older_duration) (0 : ℝ) ×ˢ
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
          Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹)) := by
  let N := I.recentNeck hpos hsmall
  let A := centeredNeckLift N q 0
  let U := centeredNeckDomain N 0
  have hU : IsOpen U := centeredNeckDomain_isOpen N 0
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A U :=
    fun x hx => (centeredNeckLift_contMDiffAt N q 0 hx).contMDiffWithinAt
  have hAi (x : E) (hx : x ∈ U) : (mfderiv (𝓡 3) (𝓡 3) A x).IsInvertible :=
    centeredNeckLift_mfderiv_isInvertible N q 0 hx
  have hmem (x : E) (hx : x ∈ U) : A x ∈ I.recent_patch.carrier :=
    centeredNeckLift_mem N q 0 hx
  have hIA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (I.identify ∘ A) U :=
    I.identify_smooth.comp hA (fun x hx => hmem x hx)
  have hIAi (x : E) (hx : x ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) (I.identify ∘ A) x).IsInvertible := by
    rw [mfderiv_comp x
      ((I.identify_smooth.contMDiffAt (I.recent_patch.carrier_open.mem_nhds
        (hmem x hx))).mdifferentiableAt (by simp))
      ((hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact (I.identify_mfderiv_invertible (A x) (hmem x hx)).comp (hAi x hx)
  have hjoin (x : E) (hx : x ∈ U) :
      (I.older_flow.metric (-I.recent_duration)).pullbackCoefficients (I.identify ∘ A) x =
        (I.recent_flow.metric (-I.recent_duration)).pullbackCoefficients A x := by
    ext v w
    change (I.older_flow.metric (-I.recent_duration)).inner (I.identify (A x))
        (mfderiv (𝓡 3) (𝓡 3) (I.identify ∘ A) x v)
        (mfderiv (𝓡 3) (𝓡 3) (I.identify ∘ A) x w) = _
    rw [mfderiv_comp x
      ((I.identify_smooth.contMDiffAt (I.recent_patch.carrier_open.mem_nhds
        (hmem x hx))).mdifferentiableAt (by simp))
      ((hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact I.joining_metric (A x) (hmem x hx) _ _
  have hs := ordinaryFlows_timeJoin (neg_lt_neg I.durations_ordered)
    (neg_lt_zero.mpr I.recent_duration_pos) I.older_flow I.recent_flow
    hU hIA hA hIAi hAi hjoin
  have hc : ContDiffOn ℝ ∞
      (fun p : ℝ × RoundCylinderCoordinates => (p.1, cylinderEuclideanEquiv.symm p.2))
      (Ioc (-I.older_duration) (0 : ℝ) ×ˢ
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
          Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹)) :=
    contDiffOn_fst.prodMk
      (cylinderEuclideanEquiv.symm.contDiff.comp_contDiffOn contDiffOn_snd)
  have hmap : MapsTo
      (fun p : ℝ × RoundCylinderCoordinates => (p.1, cylinderEuclideanEquiv.symm p.2))
      (Ioc (-I.older_duration) (0 : ℝ) ×ˢ
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
          Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹))
      (Ioc (-I.older_duration) (0 : ℝ) ×ˢ U) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    change (cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm p.2)).2 + 0 ∈
      Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹
    simpa only [ContinuousLinearEquiv.apply_symm_apply, add_zero] using hp.2.2
  have hcoef := (((hs.comp hc hmap).clm_apply
    (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ i))).clm_apply
      (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ j)))
  apply hcoef.congr
  intro p hp
  have hdom : centeredCylinderLift q 0 (cylinderEuclideanEquiv.symm p.2) ∈
      univ ×ˢ Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹ := by
    refine ⟨mem_univ _, ?_⟩
    change (cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm p.2)).2 + 0 ∈
      Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹
    simpa only [ContinuousLinearEquiv.apply_symm_apply, add_zero] using hp.2.2
  have hcoord := I.recent_patch.coordinate_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hdom)
  rw [← centeredCylinderMetric_coefficient]
  by_cases ht : p.1 < -I.recent_duration
  · have hpoint : I.recent_patch.coordinate
        (centeredCylinderLift q 0 (cylinderEuclideanEquiv.symm p.2)) ∈
          I.recent_patch.carrier := by
      rw [← I.recent_patch.coordinate_image]
      exact mem_image_of_mem _ hdom
    have hid := (I.identify_smooth.contMDiffAt
      (I.recent_patch.carrier_open.mem_nhds hpoint)).comp _ hcoord
    have heq := centeredCylinder_pullbackCoefficients (I.older_flow.metric p.1)
      (I.identify ∘ I.recent_patch.coordinate) q 0 (cylinderEuclideanEquiv.symm p.2) hid
    simp only [piecewiseTensor, Function.comp_apply, if_neg (not_le.mpr ht), if_pos ht]
    exact (congrArg (fun L => L (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)) heq).symm
  · have heq := centeredCylinder_pullbackCoefficients (I.recent_flow.metric p.1)
      I.recent_patch.coordinate q 0 (cylinderEuclideanEquiv.symm p.2) hcoord
    simp only [piecewiseTensor, Function.comp_apply, if_pos (le_of_not_gt ht), if_neg ht]
    exact (congrArg (fun L => L (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)) heq).symm

end PoincareConjecture.M45NeckGluingInput
