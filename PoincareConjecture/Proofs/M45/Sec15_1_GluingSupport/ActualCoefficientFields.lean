import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_CoefficientGerms
import PoincareConjecture.Proofs.M45.Sec15_1_GluingSupport.AffineGluingError
import PoincareConjecture.Proofs.M01.NormalizationMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

structure SmoothPositiveCoefficients (A : E → MetricCoefficient 3) (U : Set E) : Prop where
  smooth : ContDiffOn ℝ ∞ A U
  symmetric : ∀ x ∈ U, ∀ v w, A x v w = A x w v
  positive : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < A x v v
  invertible : ∀ x ∈ U, (A x).IsInvertible

theorem SmoothPositiveCoefficients.smul {A : E → MetricCoefficient 3} {U : Set E}
    (h : SmoothPositiveCoefficients A U) {r : ℝ} (hr : 0 < r) :
    SmoothPositiveCoefficients (fun x => r • A x) U := by
  refine ⟨h.smooth.const_smul r, ?_, ?_, ?_⟩
  · intro x hx v w
    change r * A x v w = r * A x w v
    rw [h.symmetric x hx v w]
  · intro x hx v hv
    exact mul_pos hr (h.positive x hx v hv)
  · intro x hx
    have hA := h.invertible x hx
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := r⁻¹ • (A x).inverse)
    · ext v
      simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
        hA.self_apply_inverse, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
        ContinuousLinearMap.id_apply]
    · ext v
      simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
        hA.inverse_apply_self, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
        ContinuousLinearMap.id_apply]

theorem smoothPositiveCoefficients_of_pullback
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : E → M} {A : E → MetricCoefficient 3} {U : Set E}
    (hU : IsOpen U) (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) f x).IsInvertible)
    {a : ℝ} (ha : 0 < a) (he : ∀ x ∈ U, A x = a • g.pullbackCoefficients f x) :
    SmoothPositiveCoefficients A U := by
  let gA := m01RescaledMetric g a ha
  have hcoeff (x : E) (hx : x ∈ U) : A x = gA.pullbackCoefficients f x := by
    rw [he x hx]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply (gA.contDiffAt_pullbackCoefficients (hf x hx)).congr_of_eventuallyEq
    exact eventually_of_mem (hU.mem_nhds hx) hcoeff
  · intro x hx v w
    rw [hcoeff x hx]
    exact gA.symm (f x) _ _
  · intro x hx v hv
    rw [hcoeff x hx]
    apply gA.pos (f x)
    intro hzero
    apply hv
    apply (hi x hx).injective
    rw [map_zero]
    exact hzero
  · intro x hx
    rw [hcoeff x hx]
    exact gA.isInvertible_pullbackCoefficients (hi x hx).injective

end M45

namespace M45NeckGluingInput

open M36 M45 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)

def recentCenteredField (z : RoundCylinderSpace) (t : ℝ) : E → MetricCoefficient 3 :=
  centeredCylinderMetric (roundCylinderPullback (I.recent_flow.metric t)
    I.recent_patch.coordinate) z.1 z.2

def olderCenteredField (z : RoundCylinderSpace) (tau : ℝ) : E → MetricCoefficient 3 :=
  centeredCylinderMetric (fun y v w => I.older_neck.neck.scale⁻¹ ^ 2 *
    roundCylinderPullback (I.older_flow.metric
      (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2))
      I.older_neck.neck.coordinate_map y v w)
    (I.olderCenteredCoordinate z).1 (I.olderCenteredCoordinate z).2

def identifiedCenteredField (z : RoundCylinderSpace) (t : ℝ) : E → MetricCoefficient 3 :=
  centeredCylinderMetric (roundCylinderPullback (I.older_flow.metric t)
    (I.identify ∘ I.recent_patch.coordinate)) z.1 z.2

theorem recentCenteredField_data (hpos : 0 < beta * epsilon)
    (hsmall : beta * epsilon < 1 / 2) (z : RoundCylinderSpace) (t : ℝ) :
    SmoothPositiveCoefficients (I.recentCenteredField z t)
      (centeredNeckDomain (I.recentNeck hpos hsmall) z.2) := by
  apply smoothPositiveCoefficients_of_pullback (I.recent_flow.metric t)
    (f := I.recentCenteredMap z) (centeredNeckDomain_isOpen _ _)
    (fun p hp => centeredNeckLift_contMDiffAt (I.recentNeck hpos hsmall) z.1 z.2 hp)
    (fun p hp => centeredNeckLift_mfderiv_isInvertible (I.recentNeck hpos hsmall) z.1 z.2 hp)
    (a := 1) (by norm_num)
  intro p hp
  simpa only [recentCenteredField, one_smul] using
    (I.recentCenteredMap_pullbackCoefficients hpos hsmall z t hp).symm

theorem olderCenteredField_data (z : RoundCylinderSpace) (tau : ℝ) :
    SmoothPositiveCoefficients (I.olderCenteredField z tau)
      (centeredNeckDomain I.older_neck.neck (I.olderCenteredCoordinate z).2) := by
  apply smoothPositiveCoefficients_of_pullback
    (I.older_flow.metric (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2))
    (f := I.olderCenteredMap z) (centeredNeckDomain_isOpen _ _)
    (fun p hp => centeredNeckLift_contMDiffAt I.older_neck.neck _ _ hp)
    (fun p hp => centeredNeckLift_mfderiv_isInvertible I.older_neck.neck _ _ hp)
    (a := I.older_neck.neck.scale⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr I.older_neck.neck.scale_pos))
  intro p hp
  exact I.olderCenteredMap_normalizedCoefficients z tau hp

theorem identifiedCenteredField_eq (hpos : 0 < beta * epsilon)
    (hsmall : beta * epsilon < 1 / 2) (z : RoundCylinderSpace) (t : ℝ) {p : E}
    (hp : p ∈ centeredNeckDomain (I.recentNeck hpos hsmall) z.2) :
    I.identifiedCenteredField z t p =
      (I.older_flow.metric t).pullbackCoefficients (I.identify ∘ I.recentCenteredMap z) p := by
  apply (centeredCylinder_pullbackCoefficients (I.older_flow.metric t)
    (I.identify ∘ I.recent_patch.coordinate) z.1 z.2 p ?_).symm
  have hpoint : centeredCylinderLift z.1 z.2 p ∈
      univ ×ˢ Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹ := ⟨mem_univ _, hp⟩
  have hmem : I.recent_patch.coordinate (centeredCylinderLift z.1 z.2 p) ∈
      I.recent_patch.carrier :=
    centeredNeckLift_mem (I.recentNeck hpos hsmall) z.1 z.2 hp
  exact (I.identify_smooth.contMDiffAt (I.recent_patch.carrier_open.mem_nhds hmem)).comp _
    (I.recent_patch.coordinate_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hpoint))

end M45NeckGluingInput

end PoincareConjecture
