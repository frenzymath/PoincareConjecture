import PoincareConjecture.Proofs.M11.SliceLabelTopology
import PoincareConjecture.Proofs.M11.BoundarylessInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem labelBox_differential_injective (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) (L.boxMap b t ht) x) := by
  intro v w hvw
  apply sub_eq_zero.mp
  by_contra hne
  have hz : mfderiv (𝓡 n) (𝓡 n) (L.boxMap b t ht) x (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have h := L.metric_eq b t ht x (v - w) (v - w)
  rw [hz, map_zero] at h
  exact (ne_of_gt ((A.box b).metric_pos t ht x.val x.property (v - w) hne)) h.symm

noncomputable def labelBoxTangentEquiv (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.ofInjectiveEndo
    (show EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) from
      (mfderiv (𝓡 n) (𝓡 n) (L.boxMap b t ht) x).toLinearMap)
    (labelBox_differential_injective A L b t ht x)).toContinuousLinearEquiv

theorem labelBox_inverse_smooth (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (labelBoxHomeomorph A L b t ht).symm
      (labelBoxHomeomorph A L b t ht).target := by
  intro p hp
  have heq : (labelBoxHomeomorph A L b t ht : (A.box b).spatial → (L.slice t).carrier) =
      L.boxMap b t ht := funext (labelBoxHomeomorph_apply A L b t ht)
  apply ContMDiffAt.contMDiffWithinAt
  apply boundaryless_inverse_smooth (labelBoxHomeomorph A L b t ht) hp
    (by rw [heq]; exact L.boxMap_smooth b t ht _)
    (labelBoxTangentEquiv A L b t ht ((labelBoxHomeomorph A L b t ht).symm p))
  rw [heq]
  rfl

theorem labelBox_localDiffeomorph (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (L.boxMap b t ht) := by
  intro x
  refine ⟨{
    toPartialEquiv := (labelBoxHomeomorph A L b t ht).toPartialEquiv
    open_source := (labelBoxHomeomorph A L b t ht).open_source
    open_target := (labelBoxHomeomorph A L b t ht).open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := labelBox_inverse_smooth A L b t ht
  }, ?_, ?_⟩
  · have heq := funext (labelBoxHomeomorph_apply A L b t ht)
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (labelBoxHomeomorph A L b t ht)
      (labelBoxHomeomorph A L b t ht).source
    rw [heq]
    exact (L.boxMap_smooth b t ht).contMDiffOn
  · change x ∈ (labelBoxHomeomorph A L b t ht).source
    rw [labelBoxHomeomorph_source]
    trivial
  · intro y _
    exact (labelBoxHomeomorph_apply A L b t ht y).symm

end PoincareConjecture.Proofs.M11
