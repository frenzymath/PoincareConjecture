import PoincareConjecture.Proofs.M11.HorizontalInclusion
import PoincareConjecture.Proofs.M11.TangentEvaluation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def boxSpatialInverseDerivative (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    letI := adaptedChartedSpace A
    TangentBundle (spacetimeModel n) X → EuclideanSpace ℝ (Fin n) := by
  letI := adaptedChartedSpace A
  letI := intervalChartedSpace (A.box b).interval
  exact fun v ↦
    (mfderiv (spacetimeModel n) (spacetimeModel n) (boxHomeomorph (A.box b)).symm v.proj v.2).2

theorem boxSpatialInverseDerivative_smooth (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    ContMDiffOn ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) (𝓡 n) ∞
      (boxSpatialInverseDerivative A b)
      ((π (SpacetimeModelVector n) (TangentSpace (spacetimeModel n) : X → Type _)) ⁻¹'
        (boxTarget A b : Set X)) := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  let := intervalChartedSpace (A.box b).interval
  have hf : ContMDiffOn (spacetimeModel n) (𝓡 n) ∞
      (fun p : X ↦ ((boxHomeomorph (A.box b)).symm p).2.val) (boxTarget A b) :=
    (box_space_smooth (A.box b)).comp_contMDiffOn (box_inverse_smooth A b)
  have hs := derivative_apply_smooth_on_open hf (boxTarget A b).isOpen
  apply hs.congr
  intro v hv
  have hchain := mfderiv_comp_apply v.proj
    ((box_space_smooth (A.box b) ((boxHomeomorph (A.box b)).symm v.proj)).mdifferentiableAt
      (by simp))
    (((box_inverse_smooth A b).contMDiffAt
      ((boxTarget A b).isOpen.mem_nhds hv)).mdifferentiableAt (by simp)) v.2
  rw [box_space_mfderiv] at hchain
  exact hchain.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_horizontal_of_inclusion (A : AdaptedMetricAtlas n X)
    (f : M → TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p)) (z : M) :
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    letI := adaptedHorizontalSmoothBundle A
    ContMDiffAt J ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
        (horizontalInclusion A ∘ f) z →
      ContMDiffAt J ((spacetimeModel n).prod (𝓡 n)) ∞ f z := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalSmoothBundle A
  intro h
  obtain ⟨b, hb⟩ := box_targets_cover A (f z).proj
  let := intervalChartedSpace (A.box b).interval
  let e := horizontalTrivialization A b
  let : MemTrivializationAtlas e := horizontalTrivialization_mem A b
  have hbase : ContMDiffAt J (spacetimeModel n) ∞ (fun y ↦ (f y).proj) z :=
    (contMDiff_proj (TangentSpace (spacetimeModel n) : X → Type _)).contMDiffAt.comp z h
  apply (e.contMDiffAt_iff (show f z ∈ e.source from hb)).mpr
  refine ⟨hbase, ?_⟩
  have hopen : IsOpen
      ((π (SpacetimeModelVector n) (TangentSpace (spacetimeModel n) : X → Type _)) ⁻¹'
        (boxTarget A b : Set X)) :=
    (boxTarget A b).isOpen.preimage
      (FiberBundle.continuous_proj (SpacetimeModelVector n)
        (TangentSpace (spacetimeModel n) : X → Type _))
  have hcoord := ((boxSpatialInverseDerivative_smooth A b).contMDiffAt
    (hopen.mem_nhds (show (horizontalInclusion A (f z)).proj ∈ boxTarget A b from hb))).comp z h
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [hbase.continuousAt.preimage_mem_nhds ((boxTarget A b).isOpen.mem_nhds hb)]
    with y hy
  have htriv := congrArg Prod.snd
    (horizontalTrivialization_apply A b (f y).proj hy (f y).2)
  have hkernel := boxHorizontalEquiv_symm_apply A b (f y).proj hy (f y).2
  have hinverse := congrArg Prod.snd (box_inverse_mfderiv A b (f y).proj hy (f y).2.val)
  exact htriv.trans (hkernel.trans hinverse)

theorem contMDiff_horizontal_iff (A : AdaptedMetricAtlas n X)
    (f : M → TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p)) :
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    letI := adaptedHorizontalSmoothBundle A
    ContMDiff J ((spacetimeModel n).prod (𝓡 n)) ∞ f ↔
      ContMDiff J ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
        (horizontalInclusion A ∘ f) := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalSmoothBundle A
  constructor
  · exact fun h ↦ (horizontalInclusion_smooth A).comp h
  · exact fun h z ↦ contMDiffAt_horizontal_of_inclusion A f z (h z)

end PoincareConjecture.Proofs.M11
