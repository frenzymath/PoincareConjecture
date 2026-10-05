import PoincareLib.Geometry.Riemannian.ScalarOperators
import PoincareLib.Geometry.Riemannian.Distance.Averaging
import PoincareLib.Geometry.Manifold.ZeroDimensional

/-!
# Smooth distance-like data and constant shifts

This module records the initial-time data consumed by the noncompact Ricci-flow
barrier argument. The construction follows Chow et al., Part III, Proposition
26.49, equations (26.128)-(26.152), printed pp. 378-385. The final constant
shift preserves the retained differential and Hessian. This basic module is
independent of the heat estimates used to construct the function.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
/-- Positive-time spacetime smoothness gives a globally smooth spatial slice. -/
lemma contMDiff_slice_of_pos {F : M → ℝ → ℝ}
    (hF : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ ↦ F p.1 p.2) (Set.univ ×ˢ Set.Ioi 0))
    {t : ℝ} (ht : 0 < t) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x ↦ F x t) := by
  exact contMDiffOn_univ.mp (hF.comp
    (contMDiffOn_id.prodMk contMDiffOn_const) (fun x _ ↦ ⟨Set.mem_univ x, ht⟩))

omit [IsManifold (𝓡 n) ∞ M] in
/-- Adding a constant preserves the retained scalar differential. -/
lemma mvfderiv_add_const {f : M → ℝ}
    (hf : MDifferentiable (𝓡 n) 𝓘(ℝ, ℝ) f) (c : ℝ) (x : M) :
    mvfderiv (𝓡 n) (fun y ↦ f y + c) x = mvfderiv (𝓡 n) f x := by
  simpa only [mvfderiv_const, add_zero] using
    mvfderiv_fun_add (hf x) (mdifferentiableAt_const (c := c))

/-- The constant shift used after heat regularization does not change the
Hessian of the retained connection. -/
lemma LeviCivitaData.hessian_add_const {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : MDifferentiable (𝓡 n) 𝓘(ℝ, ℝ) f) (c : ℝ) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    D.hessian (fun y ↦ f y + c) x v w = D.hessian f x v w := by
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    mvfderiv_add_const hf]

/-- A two-sided Hessian norm estimate gives the upper quadratic-form estimate
with the same constant and the explicitly selected metric. -/
lemma LeviCivitaData.hessian_quadratic_le_of_abs_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {C : ℝ}
    (h : ∀ x (v w : TangentSpace (𝓡 n) x),
      |D.hessian f x v w| ≤ C * g.tangentNorm x v * g.tangentNorm x w)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    D.hessian f x v v ≤ C * g.inner x v v := by
  have hv : 0 ≤ g.inner x v v := by
    by_cases h : v = 0
    · simp [h]
    · exact le_of_lt (g.pos x v h)
  have hnorm : g.tangentNorm x v * g.tangentNorm x v = g.inner x v v := by
    exact Real.mul_self_sqrt hv
  simpa only [mul_assoc, hnorm] using (le_abs_self (D.hessian f x v v)).trans (h x v v)

/-- The noncompact connected hypotheses exclude dimension zero. -/
lemma dimension_pos_of_noncompact [PreconnectedSpace M] [NoncompactSpace M] :
    0 < n := by
  by_contra hn
  have hn : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  let : Subsingleton M := Poincare.subsingleton_of_preconnected_euclidean_zero M
  exact noncompact_univ M isCompact_univ

end PoincareMT

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Initial smooth distance-like data with explicit first and second derivative
bounds.  The distance is the metric selected by `g`; no ambient metric
instance is hidden in this interface. -/
structure SmoothDistanceLike (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (O : M) where
  toFun : M → ℝ
  smooth : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  distance_lower : ∀ x, ENNReal.toReal (g.edist O x) + 1 ≤ toFun x
  distance_upper : ∀ x, toFun x ≤ bound * (ENNReal.toReal (g.edist O x) + 1)
  gradient_bound : ∀ x v,
    |mvfderiv (𝓡 n) toFun x v| ≤ bound * g.tangentNorm x v
  hessian_bound : ∀ x v,
    D.hessian toFun x v v ≤ bound * g.inner x v v

/-- The value bounds force every distance-like bound to be at least one. -/
lemma SmoothDistanceLike.one_le_bound {g : RiemannianMetric n M}
    {D : LeviCivitaData g} {O : M} (h : SmoothDistanceLike g D O) :
    1 ≤ h.bound := by
  have hl := (h.distance_lower O).trans (h.distance_upper O)
  have hd := ENNReal.toReal_nonneg (a := g.edist O O)
  nlinarith

/-- Approximation error and heat displacement add without any regularity
assumption on the distance function at the cut locus. -/
lemma abs_sub_distance_le_of_approximation (g : RiemannianMetric n M) (O : M)
    {u f : M → ℝ} {ε A : ℝ}
    (hu : ∀ x, |u x - (g.edist O x).toReal| ≤ ε)
    (hf : ∀ x, |f x - u x| ≤ A) (x : M) :
    |f x - (g.edist O x).toReal| ≤ A + ε :=
  (abs_sub_le (f x) (u x) (g.edist O x).toReal).trans (add_le_add (hf x) (hu x))

/-- The last step of Proposition 26.49: shift a time slice with additive
distance error by a constant and combine its three estimates. The numerical
bound depends only on the supplied numerical estimates. -/
noncomputable def SmoothDistanceLike.of_additive_estimates
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (O : M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {A G H : ℝ} (hA : 0 ≤ A)
    (hvalue : ∀ x, |f x - (g.edist O x).toReal| ≤ A)
    (hgradient : ∀ x v, |mvfderiv (𝓡 n) f x v| ≤ G * g.tangentNorm x v)
    (hhessian : ∀ x v, D.hessian f x v v ≤ H * g.inner x v v) :
    SmoothDistanceLike g D O where
  toFun x := f x + (A + 1)
  smooth := hf.add contMDiff_const
  bound := max (2 * A + 1) (max G H)
  bound_nonneg := le_trans (by linarith) (le_max_left _ _)
  distance_lower x := by
    have h := (abs_le.mp (hvalue x)).1
    linarith
  distance_upper x := by
    have h := (abs_le.mp (hvalue x)).2
    have hd := ENNReal.toReal_nonneg (a := g.edist O x)
    calc
      f x + (A + 1) ≤ (g.edist O x).toReal + (2 * A + 1) := by linarith
      _ ≤ (2 * A + 1) * ((g.edist O x).toReal + 1) := by nlinarith
      _ ≤ max (2 * A + 1) (max G H) * ((g.edist O x).toReal + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  gradient_bound x v := by
    rw [mvfderiv_add_const (hf.mdifferentiable (by simp))]
    exact (hgradient x v).trans (mul_le_mul_of_nonneg_right
      ((le_max_left G H).trans (le_max_right _ _)) (Real.sqrt_nonneg _))
  hessian_bound x v := by
    rw [D.hessian_add_const (hf.mdifferentiable (by simp))]
    have hv : 0 ≤ g.inner x v v := by
      by_cases h : v = 0
      · simp [h]
      · exact le_of_lt (g.pos x v h)
    exact (hhessian x v).trans (mul_le_mul_of_nonneg_right
      ((le_max_right G H).trans (le_max_right _ _)) hv)

end PoincareMT.RiemannianMetric
