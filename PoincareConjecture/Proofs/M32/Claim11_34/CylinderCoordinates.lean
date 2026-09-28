import PoincareConjecture.Proofs.M11
import PoincareConjecture.Proofs.M12.GeneralizedCylinderMetric
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.Cylinders
import PoincareConjecture.Proofs.M32.Claim11_34.IncludedMetricCoefficients

set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option backward.isDefEq.respectTransparency false in

theorem blowupPullbackCoefficient_contDiffOn
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {I : SpacetimeInterval} {origin scale : ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I.domain U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier) (a b : Fin 3) :
    ContDiffOn ℝ ∞ (blowupPullbackCoefficient e q a b)
      (I.domain ×ˢ ((extChartAt (𝓡 3) q).target ∩
        (extChartAt (𝓡 3) q).symm ⁻¹' U)) := by
  classical
  let Uo : TopologicalSpace.Opens L.sliceCarrier.carrier := ⟨U, hU⟩
  let R := Classical.choice
    (Proofs.M12.flowBoxAtlas_realize F (generalizedSpacetimeGeometry 3))
  have hI : (Proofs.M12.cylinderPhysicalInterval origin scale e.scale_pos I).domain ⊆
      F.interval := by
    rintro _ ⟨s, hs, rfl⟩
    exact cylinder_time_mem_of_nonempty_source e ⟨L.base⟩ s hs
  let m := Proofs.M12.rawCylinderMetric (U := Uo) R e hI
  let c := extChartAt (𝓡 3) q
  let W := c.target ∩ c.symm ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  intro z hz
  let j := Uo.openPartialHomeomorphSubtypeCoe ⟨⟨c.symm z.2, hz.2.2⟩⟩
  let φ : EuclideanSpace ℝ (Fin 3) → Uo := j.symm ∘ c.symm
  have htarget : j.target = U :=
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target Uo _
  have hval (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ W) :
      (φ y).val = c.symm y := by
    exact j.right_inv (by rw [htarget]; exact hy.2)
  have hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W := by
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff Uo φ W y).mp
    apply ((contMDiffOn_extChartAt_symm (n := ∞) q).mono
      (show W ⊆ c.target from inter_subset_left) y hy).congr_of_mem ?_ hy
    intro w hw
    exact hval w hw
  have hder (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ W) :
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Uo → L.sliceCarrier.carrier) (φ y)).comp
        (mfderiv (𝓡 3) (𝓡 3) φ y) = mfderiv (𝓡 3) (𝓡 3) c.symm y := by
    have heq : (Subtype.val ∘ φ) =ᶠ[𝓝 y] c.symm := by
      filter_upwards [hW.mem_nhds hy] with w hw
      exact hval w hw
    have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
    rw [mfderiv_comp y
      ((contMDiff_subtype_val (n := ∞) (φ y)).mdifferentiableAt (by simp))
      (((hφ y hy).contMDiffAt (hW.mem_nhds hy)).mdifferentiableAt (by simp))] at hd
    exact hd
  have hclock : MapsTo (fun s : ℝ => origin + s / scale) I.domain
      (Proofs.M12.cylinderPhysicalInterval origin scale e.scale_pos I).domain :=
    fun s hs => ⟨s, hs, rfl⟩
  have hτ : ContDiff ℝ ∞ (fun s : ℝ => origin + s / scale) :=
    contDiff_const.add (contDiff_id.div_const scale)
  have hcoeff := contDiffOn_clock_pullbackCoefficients_of_smoothFamily
    m.smooth hW hφ hτ hclock
  have hscalar := (contDiffOn_const (c := scale)).mul
    ((hcoeff.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))).clm_apply
      (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b)))
  apply (hscalar.congr ?_) z hz
  intro p hp
  let sid := Classical.choice (Proofs.M12.flowSlice_identification F R (origin + p.1 / scale))
  have hm := Proofs.M12.rawCylinderMetric_eq R e hI m ⟨p.1, hp.1⟩ sid (φ p.2)
    (mfderiv (𝓡 3) (𝓡 3) φ p.2 (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (mfderiv (𝓡 3) (𝓡 3) φ p.2 (EuclideanSpace.basisFun (Fin 3) ℝ b))
  have hda := congrArg (fun A => A (EuclideanSpace.basisFun (Fin 3) ℝ a)) (hder p.2 hp.2)
  have hdb := congrArg (fun A => A (EuclideanSpace.basisFun (Fin 3) ℝ b)) (hder p.2 hp.2)
  dsimp only [ContinuousLinearMap.comp_apply] at hda hdb
  rw [hda, hdb, hval p.2 hp.2] at hm
  simp only [blowupPullbackCoefficient, dif_pos hp.1]
  change _ = scale * (m.metric (origin + p.1 / scale)).inner (φ p.2)
    (mfderiv (𝓡 3) (𝓡 3) φ p.2 (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (mfderiv (𝓡 3) (𝓡 3) φ p.2 (EuclideanSpace.basisFun (Fin 3) ℝ b))
  rw [hm]
  field_simp [e.scale_pos.ne']
  rfl

end PoincareConjecture.M32
