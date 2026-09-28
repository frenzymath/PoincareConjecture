import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_PullbackPlane
import PoincareConjecture.Proofs.M44.Mathlib.ProjectionAxis











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ




theorem cylinder_axis_and_horizontal_of_rank_drop
    (L : E2 →L[ℝ] E) (hL : Function.Injective L)
    (hP : ¬ Function.Injective (cylinderHorizontalProjection.comp L)) :
    e 2 ∈ LinearMap.range L.toLinearMap ∧
      ∃ u : E, ‖u‖ = 1 ∧ cylinderHeightCovector u = 0 ∧
        u ∈ LinearMap.range L.toLinearMap := by
  let L' : E2 →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) × ℝ :=
    cylinderEuclideanEquiv.toLinearMap.comp L.toLinearMap
  have hL' : Function.Injective L' := cylinderEuclideanEquiv.injective.comp hL
  have hP' : ¬ Function.Injective (fun v => (L' v).1) := hP
  obtain ⟨a, ha⟩ := L'.exists_axis_of_not_injective_fst hL' hP'
  have haxis : (0, 1) ∈ LinearMap.range L' := ⟨a, ha⟩
  have haE : L a = e 2 := by
    apply cylinderEuclideanEquiv.injective
    rw [cylinderEuclideanEquiv_basis]
    exact ha
  obtain ⟨y, hy, q, hq⟩ := L'.exists_horizontal_of_axis_mem_range hL' (by simp) haxis
  have hq0 : L q ≠ 0 := by
    intro hz
    have hp : (cylinderEuclideanEquiv (L q)).1 = y := congrArg Prod.fst hq
    rw [hz, map_zero] at hp
    exact hy hp.symm
  have hqh : cylinderHeightCovector (L q) = 0 := congrArg Prod.snd hq
  refine ⟨⟨a, haE⟩, ‖L q‖⁻¹ • L q, norm_smul_inv_norm hq0, ?_, ?_⟩
  · rw [map_smul, hqh, smul_zero]
  · exact (LinearMap.range L.toLinearMap).smul_mem _ (LinearMap.mem_range_self L.toLinearMap q)




theorem cylinder_projection_injective_of_sectional_bounds
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) (x : E)
    (L : E2 →L[ℝ] E) (hL : Function.Injective L) (k : ℝ)
    (hlower : ∀ p ∈ LinearMap.range L.toLinearMap,
      ∀ q ∈ LinearMap.range L.toLinearMap,
      0 < g.inner x p p * g.inner x q q - (g.inner x p q) ^ 2 →
        k < D.sectionalCurvature x p q)
    (haxial : ∀ u : E, ‖u‖ = 1 → cylinderHeightCovector u = 0 →
      0 < g.inner x (e 2) (e 2) * g.inner x u u - (g.inner x (e 2) u) ^ 2 ∧
        |D.sectionalCurvature x (e 2) u| < k) :
    Function.Injective (cylinderHorizontalProjection.comp L) := by
  by_contra hP
  obtain ⟨haxis, u, hu, hh, hmem⟩ := cylinder_axis_and_horizontal_of_rank_drop L hL hP
  obtain ⟨hgram, hupper⟩ := haxial u hu hh
  have hlo := hlower _ haxis u hmem hgram
  exact (not_lt_of_ge hlo.le) ((le_abs_self _).trans_lt hupper)




theorem cylinder_plane_mem_span (L : E2 →L[ℝ] E) {v : E}
    (hv : v ∈ LinearMap.range L.toLinearMap) :
    v ∈ Submodule.span ℝ ({L (b 0), L (b 1)} : Set E) := by
  obtain ⟨w, rfl⟩ := hv
  apply Submodule.mem_span_pair.mpr
  refine ⟨w 0, w 1, ?_⟩
  change w 0 • L (b 0) + w 1 • L (b 1) = L w
  have h := congrArg L ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr w)
  simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr, map_add, map_smul] using h




theorem cylinder_projection_injective_of_plane_margin
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) (x : E)
    (L : E2 →L[ℝ] E) (hL : Function.Injective L) (k : ℝ)
    (hgram : 0 < g.inner x (L (b 0)) (L (b 0)) * g.inner x (L (b 1)) (L (b 1)) -
      (g.inner x (L (b 0)) (L (b 1))) ^ 2)
    (hlower : k < D.sectionalCurvature x (L (b 0)) (L (b 1)))
    (haxial : ∀ u : E, ‖u‖ = 1 → cylinderHeightCovector u = 0 →
      0 < g.inner x (e 2) (e 2) * g.inner x u u - (g.inner x (e 2) u) ^ 2 ∧
        |D.sectionalCurvature x (e 2) u| < k) :
    Function.Injective (cylinderHorizontalProjection.comp L) := by
  apply cylinder_projection_injective_of_sectional_bounds D x L hL k _ haxial
  intro p hp q hq hpq
  exact sectional_lower_on_physical_plane D x hgram hlower
    (cylinder_plane_mem_span L hp) (cylinder_plane_mem_span L hq) hpq

end PoincareConjecture.M44
