import PoincareConjecture.Definitions.M14Exponential
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.NormNum









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem tangent_transport {q r : G.Point} (h : q = r)
    (v : TangentSpace (spacetimeModel n) q) :
    (show SpacetimeModelVector n from
      (h ▸ v : TangentSpace (spacetimeModel n) r)) = v := by
  cases h
  rfl



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

end PoincareConjecture.M14
