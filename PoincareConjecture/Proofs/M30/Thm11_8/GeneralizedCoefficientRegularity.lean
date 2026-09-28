import PoincareConjecture.Proofs.M30.Generalized.OrdinaryExtraction
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricCoefficients
import PoincareConjecture.Definitions.Ch11.BlowupLimits











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold




theorem contDiffOn_generalized_pullback_coefficient
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ)
    (q : G.limit.carrier.carrier)
    {V : Set (EuclideanSpace ℝ (Fin 3))}
    (hV : IsOpen V) (hVc : V ⊆ (extChartAt (𝓡 3) q).target)
    (hstage : (extChartAt (𝓡 3) q).symm '' V ⊆ G.exhaustion.space k)
    (a b : Fin 3) :
    ContDiffOn ℝ ∞ (blowupPullbackCoefficient (G.embedding k) q a b)
      (Icc (-G.exhaustion.time k) 0 ×ˢ V) := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : Nonempty G.limit.sliceCarrier.carrier := ⟨G.limit.base⟩
  let W : SpacetimeInterval := {
    domain := Icc (-G.exhaustion.time k) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-G.exhaustion.time k,
      ⟨le_rfl, neg_nonpos.mpr (G.exhaustion.time_pos k).le⟩,
      0, ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩,
      (neg_lt_zero.mpr (G.exhaustion.time_pos k)).ne⟩ }
  let Y : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space k, G.exhaustion.space_open k⟩
  obtain ⟨P, hP⟩ := Cylinder.exists_ordinaryFlow (J := W) (U := Y) (G.embedding k)
    (Cylinder.physicalInterval_subset (J := W) (U := Y) (G.embedding k))
  let c := extChartAt (𝓡 3) q
  let psi : E → Y := fun x => if hx : c.symm x ∈ Y then ⟨c.symm x, hx⟩
    else ⟨G.limit.base, G.exhaustion.base_mem k⟩
  have hval (x : E) (hx : x ∈ V) : (psi x).val = c.symm x := by
    have hy : c.symm x ∈ Y := hstage (mem_image_of_mem c.symm hx)
    simp only [psi, dif_pos hy]
  have hnear (x : E) (hx : x ∈ V) :
      (Subtype.val : Y → G.limit.sliceCarrier.carrier) ∘ psi =ᶠ[𝓝 x] c.symm := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hval y hy
  have hpsi (x : E) (hx : x ∈ V) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ psi x := by
    apply (ContMDiffAt.subtypeVal_comp_iff Y psi x).mp
    exact ((contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hVc hx))).congr_of_eventuallyEq
        (hnear x hx)
  have hsmooth := P.smooth.contDiffOn_spacetime_pullbackCoefficients_within hV
    (fun x hx => (hpsi x hx).contMDiffWithinAt)
  have hscalar : ContDiffOn ℝ ∞
      (fun p : ℝ × E => (P.metric p.1).pullbackCoefficients psi p.2
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) (W.domain ×ˢ V) :=
    (hsmooth.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  apply hscalar.congr
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  change t ∈ Icc (-G.exhaustion.time k) 0 at ht
  have hd := (mfderiv_comp x
    ((contMDiff_subtype_val (U := Y) (I := 𝓡 3) (n := ∞) (psi x)).mdifferentiableAt
      (by simp)) ((hpsi x hx).mdifferentiableAt (by simp))).symm.trans
        (hnear x hx).mfderiv_eq
  simp only [blowupPullbackCoefficient, dif_pos ht]
  change _ = (P.metric t).inner (psi x)
    (mfderiv (𝓡 3) (𝓡 3) psi x (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (mfderiv (𝓡 3) (𝓡 3) psi x (EuclideanSpace.basisFun (Fin 3) ℝ b))
  rw [hP t ht]
  erw [congrArg (fun L => L (EuclideanSpace.basisFun (Fin 3) ℝ a)) hd,
    congrArg (fun L => L (EuclideanSpace.basisFun (Fin 3) ℝ b)) hd, hval x hx]
  rfl

end PoincareConjecture.M30
