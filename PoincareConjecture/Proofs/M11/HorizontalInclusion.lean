import PoincareConjecture.Proofs.M11.HorizontalBundle
import PoincareConjecture.Proofs.M11.SpatialTangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem horizontalTrivialization_apply (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (p : X) (hp : p ∈ (boxHomeomorph (A.box b)).target) (v : adaptedHorizontal A p) :
    letI := adaptedHorizontalTopology A
    horizontalTrivialization A b (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p v) =
      (p, (boxHorizontalEquiv A b p hp).symm v) :=
  linearPretrivialization_apply (boxTarget A b)
    (fun p hp ↦ (boxHorizontalEquiv A b p hp).symm) p hp v

noncomputable def horizontalInclusion (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p) →
      TangentBundle (spacetimeModel n) X :=
  fun v ↦ TotalSpace.mk' (SpacetimeModelVector n) v.proj v.2.val

theorem horizontalInclusion_smooth (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    letI := adaptedHorizontalSmoothBundle A
    ContMDiff ((spacetimeModel n).prod (𝓡 n))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞ (horizontalInclusion A) := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalSmoothBundle A
  intro z
  obtain ⟨b, hb⟩ := box_targets_cover A z.proj
  let := intervalChartedSpace (A.box b).interval
  let e := horizontalTrivialization A b
  let : MemTrivializationAtlas e := horizontalTrivialization_mem A b
  have hz : z ∈ e.source := hb
  have hid : ContMDiffAt ((spacetimeModel n).prod (𝓡 n))
      ((spacetimeModel n).prod (𝓡 n)) ∞ id z := contMDiffAt_id
  have hcoords := (e.contMDiffAt_iff hz).mp hid
  have hinv := ((box_inverse_smooth A b).contMDiffAt
    ((boxHomeomorph (A.box b)).open_target.mem_nhds hb)).comp z hcoords.1
  have hpush := (box_spatial_push_smooth A b).contMDiffAt.comp z (hinv.prodMk hcoords.2)
  apply hpush.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hz] with w hw
  have hwb : w.proj ∈ (boxHomeomorph (A.box b)).target := hw
  have hcoord : (e w).2 = (boxHorizontalEquiv A b w.proj hwb).symm w.2 :=
    congrArg Prod.snd (horizontalTrivialization_apply A b w.proj hwb w.2)
  have hvec := congrArg (fun v : adaptedHorizontal A w.proj ↦ v.val)
    ((boxHorizontalEquiv A b w.proj hwb).apply_symm_apply w.2)
  rw [boxHorizontalEquiv_apply] at hvec
  refine TotalSpace.ext (boxHomeomorph_right_inv (A.box b) hwb).symm ?_
  apply heq_of_eq
  change w.2.val = boxTangentEquiv A b ((boxHomeomorph (A.box b)).symm w.proj) (0, (e w).2)
  rw [hcoord]
  exact hvec.symm

end PoincareConjecture.Proofs.M11
