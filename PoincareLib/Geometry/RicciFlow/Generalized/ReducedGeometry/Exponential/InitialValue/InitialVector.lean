import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.NormNum

/-!
# Recovering the initial vector of a selected exponential branch

Morgan-Tian Lemma 6.8, p. 108, and Definition 6.17, p. 113. The frozen
family records the initial within derivative as twice the initial vector.
Consequently agreement of positive-length branches determines that vector.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem tangent_transport {q r : G.Point} (h : q = r)
    (v : TangentSpace (spacetimeModel n) q) :
    (show SpacetimeModelVector n from
      (h ▸ v : TangentSpace (spacetimeModel n) r)) = v := by
  cases h
  rfl

/-- The selected square-root path is the same branch throughout its closed
interval, Morgan-Tian Definition 6.17, p. 113. -/
theorem exponential_square_curve_eq (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    {r : ℝ} (hr : r ∈ M14SqrtParameterInterval 0 (s ^ 2)) :
    (E.square_path Z s hs hpos).curve r = E.gamma Z r := by
  have hr0 : 0 ≤ r := by simpa [M14SqrtParameterInterval] using hr.1
  have hrs : r ≤ s := by
    simpa [M14SqrtParameterInterval, Real.sqrt_sq hpos.le] using hr.2
  have hsq : r ^ 2 ∈ Set.Icc 0 (s ^ 2) :=
    ⟨sq_nonneg r, (sq_le_sq₀ hr0 hpos.le).mpr hrs⟩
  calc
    (E.square_path Z s hs hpos).curve r =
        (E.path Z s hs hpos).curve (r ^ 2) :=
      (E.square_path Z s hs hpos).agrees r hr
    _ = E.gamma Z (Real.sqrt (r ^ 2)) := E.path_coherent Z s hs hpos _ hsq
    _ = E.gamma Z r := by rw [Real.sqrt_sq hr0]

/-- The initial derivative, read in the fixed tangent model, is twice the
initial horizontal vector; Morgan-Tian Lemma 6.8, p. 108. -/
theorem exponential_initial_derivative (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    (show SpacetimeModelVector n from
      mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
        (E.square_path Z s hs hpos).curve (M14SqrtParameterInterval 0 (s ^ 2))
        0 (1 : ℝ)) = (2 : ℝ) • Z.val := by
  obtain ⟨hbase, hderiv⟩ := E.initial_derivative Z s hs hpos
  have hmodel := congrArg
    (fun v : TangentSpace (spacetimeModel n) x =>
      (show SpacetimeModelVector n from v)) hderiv
  simpa only [tangent_transport] using hmodel

/-- Equal square-root branches on a positive interval have equal initial
vectors, Morgan-Tian Lemma 6.8 and Definition 6.17, pp. 108, 113. -/
theorem initialVector_eq_of_square_branches_eqOn (E : M14ExponentialFamily G T x)
    {Z W : G.Horizontal x} {s : ℝ}
    (hZ : (Z, s) ∈ E.domain) (hW : (W, s) ∈ E.domain) (hpos : 0 < s)
    (h : Set.EqOn (E.gamma Z) (E.gamma W) (M14SqrtParameterInterval 0 (s ^ 2))) :
    Z = W := by
  have hcurves : Set.EqOn (E.square_path Z s hZ hpos).curve
      (E.square_path W s hW hpos).curve (M14SqrtParameterInterval 0 (s ^ 2)) := by
    intro r hr
    exact (exponential_square_curve_eq E Z hZ hpos hr).trans
      ((h hr).trans (exponential_square_curve_eq E W hW hpos hr).symm)
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
    exact ⟨by simp, Real.sqrt_nonneg _⟩
  have hd := mfderivWithin_congr_of_mem
    (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n) hcurves hzero
  have hv := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1) hd
  have hvectors : (2 : ℝ) • Z.val = (2 : ℝ) • W.val :=
    (exponential_initial_derivative E Z hZ hpos).symm.trans
      (hv.trans (exponential_initial_derivative E W hW hpos))
  apply Subtype.ext
  exact smul_right_injective (SpacetimeModelVector n)
    (by norm_num : (2 : ℝ) ≠ 0) hvectors

/-- Equal backward-time branches recover the same initial vector, using the
square-root reparameterization of Morgan-Tian equations (6.1)-(6.2), p. 106. -/
theorem initialVector_eq_of_backward_branches_eqOn
    (E : M14ExponentialFamily G T x) {Z W : G.Horizontal x} {s : ℝ}
    (hZ : (Z, s) ∈ E.domain) (hW : (W, s) ∈ E.domain) (hpos : 0 < s)
    (h : Set.EqOn (fun t => E.gamma Z (Real.sqrt t))
      (fun t => E.gamma W (Real.sqrt t)) (Set.Icc 0 (s ^ 2))) : Z = W := by
  apply initialVector_eq_of_square_branches_eqOn E hZ hW hpos
  intro r hr
  have hr0 : 0 ≤ r := by simpa [M14SqrtParameterInterval] using hr.1
  have hrs : r ≤ s := by
    simpa [M14SqrtParameterInterval, Real.sqrt_sq hpos.le] using hr.2
  have heq := h (show r ^ 2 ∈ Set.Icc 0 (s ^ 2) from
    ⟨sq_nonneg r, (sq_le_sq₀ hr0 hpos.le).mpr hrs⟩)
  simpa only [Real.sqrt_sq hr0] using heq

end PoincareMT.M14
