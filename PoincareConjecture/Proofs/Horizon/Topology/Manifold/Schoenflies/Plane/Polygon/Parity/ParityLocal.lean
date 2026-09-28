import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Parity.CrossingLocal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Parity.CrossingParity
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.BoundaryBasics
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

namespace Poincare.Manifold.Schoenflies.Plane

theorem lineSideParity_prev_eq_of_vertex_height
    {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ)
    (he : ∀ j, H (p j) ≠ H (p (finRotate n j))) (i : Fin n) {q : E}
    (hq : H q = H (p i)) :
    lineSideParity X H (p ((finRotate n).symm i))
      (p (finRotate n ((finRotate n).symm i))) q =
        lineSideParity X H (p i) (p (finRotate n i)) q := by
  have hi : H (p ((finRotate n).symm i)) ≠ H (p i) := by
    simpa only [Equiv.apply_symm_apply] using he ((finRotate n).symm i)
  simp only [lineSideParity, Equiv.apply_symm_apply, hq,
    lineLevelPoint_left, lineLevelPoint_right H hi]

theorem sum_weighted_heightStep_equiv {I : Type*} [Fintype I]
    (e : I ≃ I) (w : I → ZMod 2) (h : I → ℝ) (y : ℝ) :
    ∑ i, w i * (heightStep (h i) y + heightStep (h (e i)) y) =
      ∑ i, (w i + w (e.symm i)) * heightStep (h i) y := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    Equiv.sum_comp e (fun i => w (e.symm i) * heightStep (h i) y)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem polygonCrossingParity_eventually_eq (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ)
    (hX : Continuous X) (hH : Continuous H)
    (hcoords : Function.Injective (fun x => (X x, H x)))
    (he : ∀ i, H (p i) ≠ H (p (finRotate n i))) {q : E}
    (hq : q ∉ p.boundary ℝ) :
    ∀ᶠ z in 𝓝 q, polygonCrossingParity p X H z = polygonCrossingParity p X H q := by
  let w : Fin n → ZMod 2 := fun i => lineSideParity X H (p i) (p (finRotate n i)) q
  have hedges : ∀ᶠ z in 𝓝 q, ∀ i, segmentRayParity X H (p i) (p (finRotate n i)) z =
      w i * (heightStep (H (p i)) (H z) + heightStep (H (p (finRotate n i))) (H z)) := by
    apply eventually_all.mpr
    intro i
    apply segmentRayParity_eventually_eq_factor X H hX hH hcoords (he i)
    intro hmem
    apply hq
    apply polygon_edgeSet_subset_boundary p i
    rwa [polygon_edgeSet_eq_segment]
  have hvertices : ∀ᶠ z in 𝓝 q, ∀ i,
      (w i + w ((finRotate n).symm i)) * heightStep (H (p i)) (H z) =
        (w i + w ((finRotate n).symm i)) * heightStep (H (p i)) (H q) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : H (p i) = H q
    · have hw : w ((finRotate n).symm i) = w i :=
        lineSideParity_prev_eq_of_vertex_height p X H he i hi.symm
      exact Eventually.of_forall fun z => by
        rw [hw, CharTwo.add_self_eq_zero]
        simp only [zero_mul]
    · filter_upwards [heightStep_eventually_eq hH.continuousAt hi] with z hz
      rw [hz]
  filter_upwards [hedges, hvertices] with z hz hv
  calc
    polygonCrossingParity p X H z =
        ∑ i, w i * (heightStep (H (p i)) (H z) +
          heightStep (H (p (finRotate n i))) (H z)) :=
      Finset.sum_congr rfl fun i _ => hz i
    _ = ∑ i, (w i + w ((finRotate n).symm i)) * heightStep (H (p i)) (H z) :=
      sum_weighted_heightStep_equiv (finRotate n) w (fun i => H (p i)) (H z)
    _ = ∑ i, (w i + w ((finRotate n).symm i)) * heightStep (H (p i)) (H q) :=
      Finset.sum_congr rfl fun i _ => hv i
    _ = ∑ i, w i * (heightStep (H (p i)) (H q) +
        heightStep (H (p (finRotate n i))) (H q)) :=
      (sum_weighted_heightStep_equiv (finRotate n) w (fun i => H (p i)) (H q)).symm
    _ = polygonCrossingParity p X H q :=
      Finset.sum_congr rfl fun i _ => (hedges.self_of_nhds i).symm

theorem isLocallyConstant_polygonCrossingParity (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ)
    (hX : Continuous X) (hH : Continuous H)
    (hcoords : Function.Injective (fun x => (X x, H x)))
    (he : ∀ i, H (p i) ≠ H (p (finRotate n i))) :
    IsLocallyConstant (fun q : {q : E // q ∉ p.boundary ℝ} =>
      polygonCrossingParity p X H q) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro q
  exact continuous_subtype_val.continuousAt.eventually
    (polygonCrossingParity_eventually_eq p X H hX hH hcoords he q.property)

theorem polygonCrossingParity_eq_of_isPreconnected (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ)
    (hX : Continuous X) (hH : Continuous H)
    (hcoords : Function.Injective (fun x => (X x, H x)))
    (he : ∀ i, H (p i) ≠ H (p (finRotate n i)))
    {s : Set E} (hs : IsPreconnected s) (havoid : s ⊆ (p.boundary ℝ)ᶜ)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    polygonCrossingParity p X H x = polygonCrossingParity p X H y := by
  let := isPreconnected_iff_preconnectedSpace.mp hs
  have hloc : IsLocallyConstant (fun z : s => polygonCrossingParity p X H z) :=
    (isLocallyConstant_polygonCrossingParity p X H hX hH hcoords he).comp_continuous
      (continuous_subtype_val.subtype_mk (fun z : s => havoid z.property))
  exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

end Poincare.Manifold.Schoenflies.Plane
