import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.ExponentialGram
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StablePrefix
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Domain.JointBranches
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.MetricBases
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.GramDeterminantSourceEquiv

/-!
# Constant source normalization for the actual Gram Jacobian

A fixed source equivalence changes the metric Jacobian by the
absolute value of its determinant. At a joint endpoint the actual
bijective exponential differential provides a source change whose
images are orthonormal. Morgan-Tian Lemma 6.71, p. 141, and
Proposition 6.81, pp. 145-146.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- A constant source change has its exact determinant factor in the
actual exponential metric Jacobian, Lemma 6.71, p. 141. -/
theorem exponentialJacobian_source_equiv (E : M14ExponentialFamily G T x)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (C : G.Horizontal x ≃ₗ[ℝ] G.Horizontal x) (Z : G.Horizontal x) (s : ℝ) :
    exponentialJacobian E (fun i => C (b i)) Z s =
      |LinearMap.det C.toLinearMap| * exponentialJacobian E b Z s := by
  let A := (exponentialDifferential E Z s).toLinearMap
  let B := ((G.spacetime.horizontalMetric.inner (E.gamma Z s)).toBilinForm).comp A A
  exact sqrt_max_det_bilin_source_equiv b B C

/-- The source factor of a linear equivalence is nonzero, including
dimension zero, as required in Proposition 6.81, pp. 145-146. -/
theorem exponentialJacobian_source_factor_ne_zero
    (C : G.Horizontal x ≃ₗ[ℝ] G.Horizontal x) : |LinearMap.det C.toLinearMap| ≠ 0 :=
  abs_ne_zero.mpr C.isUnit_det'.ne_zero

/-- At a joint endpoint, fixed source directions can be chosen whose
actual differential images form an orthonormal endpoint basis,
Proposition 6.28, p. 117, and Proposition 6.81, pp. 145-146. -/
theorem exists_exponentialJacobian_source_normalization
    (E : M14ExponentialFamily G T x) (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (hz : (Z, s) ∈ M14JointDomain G E) :
    ∃ (C : G.Horizontal x ≃ₗ[ℝ] G.Horizontal x)
      (e : Module.Basis (Fin n) ℝ (G.Horizontal (E.gamma Z s))),
      (∀ i j, G.spacetime.horizontalMetric.inner (E.gamma Z s) (e i) (e j) =
        if i = j then 1 else 0) ∧ ∀ i, E.differential Z s hs (C (b i)) = e i := by
  obtain ⟨H, hZH⟩ := jointDomain_stableSet E hz
  have hbij : Function.Bijective (E.differential Z s hs) := by
    have hstable := (H.carrier_exact Z).mp hZH
    unfold M14StableInitialVector at hstable
    rw [Real.sqrt_sq hpos.le] at hstable
    exact hstable.choose_spec.1
  let D := LinearEquiv.ofBijective (E.differential Z s hs).toLinearMap hbij
  obtain ⟨e, he⟩ := exists_orthonormal_horizontalBasis G (E.gamma Z s)
  let C := (b.equiv e (Equiv.refl (Fin n))).trans D.symm
  refine ⟨C, e, he, ?_⟩
  intro i
  change D (D.symm (b.equiv e (Equiv.refl (Fin n)) (b i))) = e i
  rw [D.apply_symm_apply, Module.Basis.equiv_apply]
  rfl

end PoincareMT.M14
