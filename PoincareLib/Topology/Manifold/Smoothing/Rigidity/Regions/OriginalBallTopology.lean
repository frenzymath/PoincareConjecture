import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLInterior
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Whole ambient topology of the actual original PL ball

The given ball map is an embedding on the full cube. Its original
finite coordinate patches identify ambient interior in both directions,
so the entire prescribed boundary is the ambient frontier. See044.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.ChartwisePLBall

local notation "V3" => (Fin 3 → ℝ)
local notation "C" => closedBall (0 : V3) 1
local notation "Q" => sphere (0 : V3) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {D S : Set X}

/-- The actual total map has exactly the whole ball as cube image.
See rigidity044, section2. -/
theorem image_closedBall (b : ChartwisePLBall e D S) : b.map '' C = D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [b.map_eq ⟨z, hz⟩]
    exact (b.parametrization ⟨z, hz⟩).property
  · intro hx
    refine ⟨b.parametrization.symm ⟨x, hx⟩,
      (b.parametrization.symm ⟨x, hx⟩).property, ?_⟩
    rw [b.map_eq, b.parametrization.apply_symm_apply]

/-- The same total map restricted to the entire cube is an actual
embedding in the original space. See rigidity044, section2. -/
theorem isEmbedding (b : ChartwisePLBall e D S) :
    Topology.IsEmbedding (fun z : C => b.map z) := by
  have hfun : (fun z : C => b.map z) = (fun z : C => (b.parametrization z : X)) :=
    funext b.map_eq
  rw [hfun]
  exact Topology.IsEmbedding.subtypeVal.comp b.parametrization.isEmbedding

/-- The complete original ball carrier is compact. See044, section2. -/
theorem isCompact (b : ChartwisePLBall e D S) : IsCompact D := by
  rw [← b.image_closedBall]
  exact (isCompact_closedBall (0 : V3) 1).image_of_continuousOn b.piecewiseAffine.continuousOn

/-- Both directions of the frozen boundary field identify the
entire marked boundary as the actual cube-rim image. See044. -/
theorem image_sphere (b : ChartwisePLBall e D S) : b.map '' Q = S := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [b.map_eq ⟨z, sphere_subset_closedBall hz⟩]
    exact (b.boundary_eq ⟨z, sphere_subset_closedBall hz⟩).mpr hz
  · intro hx
    let z : C := b.parametrization.symm ⟨x, b.boundary_subset hx⟩
    have hval : (b.parametrization z : X) = x :=
      congrArg Subtype.val (b.parametrization.apply_symm_apply ⟨x, b.boundary_subset hx⟩)
    have hzQ : (z : V3) ∈ Q := (b.boundary_eq z).mp (by rw [hval]; exact hx)
    exact ⟨z, hzQ, (b.map_eq z).trans hval⟩

/-- The original ball parameter preserves and reflects ambient
interior, by actual equal-dimensional PL coordinates. See044. -/
theorem mem_interior_iff (b : ChartwisePLBall e D S) (x : C) :
    (b.parametrization x : X) ∈ interior D ↔ (x : V3) ∈ ball 0 1 := by
  have h := b.piecewiseAffine.mem_interior_image_iff rfl b.isEmbedding x
  rwa [b.image_closedBall, b.map_eq x, interior_closedBall _ one_ne_zero] at h

/-- The image of the whole open cube is exactly the ambient ball
interior, including the converse direction. See044, section2. -/
theorem image_ball (b : ChartwisePLBall e D S) : b.map '' ball (0 : V3) 1 = interior D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [b.map_eq ⟨z, ball_subset_closedBall hz⟩]
    exact (b.mem_interior_iff ⟨z, ball_subset_closedBall hz⟩).mpr hz
  · intro hx
    let z : C := b.parametrization.symm ⟨x, interior_subset hx⟩
    have hval : (b.parametrization z : X) = x :=
      congrArg Subtype.val (b.parametrization.apply_symm_apply ⟨x, interior_subset hx⟩)
    have hz : (z : V3) ∈ ball 0 1 := (b.mem_interior_iff z).mp (by rw [hval]; exact hx)
    exact ⟨z, hz, (b.map_eq z).trans hval⟩

/-- Every point away from the complete marked rim, and only such
a ball point, is in its original ambient interior. See044. -/
theorem interior_eq_sdiff (b : ChartwisePLBall e D S) : interior D = D \ S := by
  have hinj : InjOn b.map C := by
    intro x hx y hy hxy
    have h : (⟨x, hx⟩ : C) = ⟨y, hy⟩ := b.isEmbedding.injective hxy
    exact congrArg Subtype.val h
  rw [← b.image_ball, ← closedBall_sdiff_sphere,
    hinj.image_sdiff_subset sphere_subset_closedBall, b.image_closedBall, b.image_sphere]

/-- The whole marked ball boundary is its actual original ambient
frontier. No additional boundary field is assumed. See044. -/
theorem frontier_eq [T2Space X] (b : ChartwisePLBall e D S) : frontier D = S := by
  rw [frontier, b.isCompact.isClosed.closure_eq, b.interior_eq_sdiff]
  ext x
  change (x ∈ D ∧ ¬ (x ∈ D ∧ x ∉ S)) ↔ x ∈ S
  constructor
  · intro hx
    by_contra hnot
    exact hx.2 ⟨hx.1, hnot⟩
  · exact fun hx => ⟨b.boundary_subset hx, fun h => h.2 hx⟩

/-- The actual original ball interior is dense in its whole compact
carrier. Continuity is used only on the full closed cube. See044. -/
theorem closure_interior [T2Space X] (b : ChartwisePLBall e D S) :
    closure (interior D) = D := by
  rw [← b.image_ball]
  apply Subset.antisymm
  · apply closure_minimal _ b.isCompact.isClosed
    exact (image_mono ball_subset_closedBall).trans b.image_closedBall.subset
  · have hc : ContinuousOn b.map (closure (ball (0 : V3) 1)) := by
      rw [closure_ball _ one_ne_zero]
      exact b.piecewiseAffine.continuousOn
    have h := hc.image_closure
    rwa [closure_ball _ one_ne_zero, b.image_closedBall] at h

/-- The actual ambient interior of the full original ball is
connected and nonempty. See044, section3. -/
theorem isConnected_interior (b : ChartwisePLBall e D S) : IsConnected (interior D) := by
  rw [← b.image_ball]
  exact (isConnected_ball (x := (0 : V3)) zero_lt_one).image b.map
    (b.piecewiseAffine.continuousOn.mono ball_subset_closedBall)

/-- The ambient frontier of that connected open interior is the
same complete original marked sphere. See044, section3. -/
theorem frontier_interior [T2Space X] (b : ChartwisePLBall e D S) :
    frontier (interior D) = S := by
  have h := b.frontier_eq
  rw [frontier, b.isCompact.isClosed.closure_eq] at h
  rw [frontier, b.closure_interior, interior_interior]
  exact h

/-- A ball inside R whose whole marked boundary is interior to R
lies entirely in that original interior. See044, section3. -/
theorem subset_interior (b : ChartwisePLBall e D S) {R : Set X}
    (hDR : D ⊆ R) (hS : S ⊆ interior R) : D ⊆ interior R := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact hS hxS
  · apply interior_mono hDR
    rw [b.interior_eq_sdiff]
    exact ⟨hx, hxS⟩

end PoincareMT.M76.ChartwisePLBall
