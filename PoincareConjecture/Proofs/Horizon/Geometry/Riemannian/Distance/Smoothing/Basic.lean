import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Averaging
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ZeroDimensional










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

lemma contMDiff_slice_of_pos {F : M → ℝ → ℝ}
    (hF : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ ↦ F p.1 p.2) (Set.univ ×ˢ Set.Ioi 0))
    {t : ℝ} (ht : 0 < t) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x ↦ F x t) := by
  exact contMDiffOn_univ.mp (hF.comp
    (contMDiffOn_id.prodMk contMDiffOn_const) (fun x _ ↦ ⟨Set.mem_univ x, ht⟩))

omit [IsManifold (𝓡 n) ∞ M] in

lemma mvfderiv_add_const {f : M → ℝ}
    (hf : MDifferentiable (𝓡 n) 𝓘(ℝ, ℝ) f) (c : ℝ) (x : M) :
    mvfderiv (𝓡 n) (fun y ↦ f y + c) x = mvfderiv (𝓡 n) f x := by
  simpa only [mvfderiv_const, add_zero] using
    mvfderiv_fun_add (hf x) (mdifferentiableAt_const (c := c))



lemma LeviCivitaData.hessian_add_const {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : MDifferentiable (𝓡 n) 𝓘(ℝ, ℝ) f) (c : ℝ) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    D.hessian (fun y ↦ f y + c) x v w = D.hessian f x v w := by
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    mvfderiv_add_const hf]



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


lemma dimension_pos_of_noncompact [PreconnectedSpace M] [NoncompactSpace M] :
    0 < n := by
  by_contra hn
  have hn : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  let : Subsingleton M := Poincare.subsingleton_of_preconnected_euclidean_zero M
  exact noncompact_univ M isCompact_univ

end PoincareConjecture

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




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


lemma SmoothDistanceLike.one_le_bound {g : RiemannianMetric n M}
    {D : LeviCivitaData g} {O : M} (h : SmoothDistanceLike g D O) :
    1 ≤ h.bound := by
  have hl := (h.distance_lower O).trans (h.distance_upper O)
  have hd := ENNReal.toReal_nonneg (a := g.edist O O)
  nlinarith



lemma abs_sub_distance_le_of_approximation (g : RiemannianMetric n M) (O : M)
    {u f : M → ℝ} {ε A : ℝ}
    (hu : ∀ x, |u x - (g.edist O x).toReal| ≤ ε)
    (hf : ∀ x, |f x - u x| ≤ A) (x : M) :
    |f x - (g.edist O x).toReal| ≤ A + ε :=
  (abs_sub_le (f x) (u x) (g.edist O x).toReal).trans (add_le_add (hf x) (hu x))




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

end PoincareConjecture.RiemannianMetric
