import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Christoffel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.PointwiseTransition













set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem eventually_fderiv_fderiv_eq_of_metric_pullback
    {A B : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (hA : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ A y)
    (hB : ∀ᶠ y in 𝓝 (f x), ContDiffAt ℝ ∞ B y)
    (hAi : (A x).IsInvertible) (hBi : (B (f x)).IsInvertible)
    (hBsymm : ∀ᶠ y in 𝓝 (f x), ∀ u v, B y u v = B y v u)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      A y u v = B (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) :
    ∀ᶠ y in 𝓝 x, fderiv ℝ (fderiv ℝ f) y =
      transitionHessianPolynomial
        (CoordinateExponential.christoffelBilinear A y,
          (CoordinateExponential.christoffelBilinear B (f y), fderiv ℝ f y)) := by
  have hfc := hf.self_of_nhds.continuousAt
  have hopen : IsOpen {Q : E →L[ℝ] E →L[ℝ] ℝ | Q.IsInvertible} :=
    ContinuousLinearEquiv.isOpen
  have hAi' : ∀ᶠ y in 𝓝 x, (A y).IsInvertible :=
    hA.self_of_nhds.continuousAt.eventually (hopen.mem_nhds hAi)
  have hBi' : ∀ᶠ y in 𝓝 (f x), (B y).IsInvertible :=
    hB.self_of_nhds.continuousAt.eventually (hopen.mem_nhds hBi)
  filter_upwards [hf, hA, hfc.eventually hB, hAi', hfc.eventually hBi',
    hfc.eventually hBsymm, hmetric.eventually_nhds] with y hfy hAy hBy hAiy hBiy hsymm hm
  exact fderiv_fderiv_eq_transitionHessianPolynomial
    (hAy.differentiableAt (by simp)) (hBy.differentiableAt (by simp))
    hAiy hBiy hsymm hfy
    (surjective_of_pullback_isInvertible hAiy hm.self_of_nhds) hm




theorem exists_finite_metric_isometry_jet_bound_at
    {ι : Type*} {A B : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    {f : ι → E → E} (x : ι → E)
    (hf : ∀ i, ∀ᶠ y in 𝓝 (x i), ContDiffAt ℝ ∞ (f i) y)
    (hA : ∀ i, ∀ᶠ y in 𝓝 (x i), ContDiffAt ℝ ∞ (A i) y)
    (hB : ∀ i, ∀ᶠ y in 𝓝 (f i (x i)), ContDiffAt ℝ ∞ (B i) y)
    (r : ℕ) (hr : 1 ≤ r)
    (hAj : ∃ C : ℝ, ∀ i j, j ≤ r → ‖iteratedFDeriv ℝ j (A i) (x i)‖ ≤ C)
    (hBj : ∃ C : ℝ, ∀ i j, j ≤ r → ‖iteratedFDeriv ℝ j (B i) (f i (x i))‖ ≤ C)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hAlow : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (x i) v v)
    (hBlow : ∀ i v, b * ‖v‖ ^ 2 ≤ B i (f i (x i)) v v)
    (hzero : ∃ C : ℝ, ∀ i, ‖f i (x i)‖ ≤ C)
    (hBsymm : ∀ i, ∀ᶠ y in 𝓝 (f i (x i)), ∀ u v, B i y u v = B i y v u)
    (hmetric : ∀ i, ∀ᶠ y in 𝓝 (x i), ∀ u v,
      A i y u v = B i (f i y) (fderiv ℝ (f i) y u) (fderiv ℝ (f i) y v)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i j, j ≤ r + 1 →
      ‖iteratedFDeriv ℝ j (f i) (x i)‖ ≤ C := by
  have hf₀ (i : ι) : ContDiffAt ℝ ∞ (f i) (x i) := (hf i).self_of_nhds
  have hA₀ (i : ι) : ContDiffAt ℝ ∞ (A i) (x i) := (hA i).self_of_nhds
  have hB₀ (i : ι) : ContDiffAt ℝ ∞ (B i) (f i (x i)) := (hB i).self_of_nhds
  have hAi (i : ι) : (A i (x i)).IsInvertible :=
    isInvertible_of_uniformEllipticity ha (hAlow i)
  have hBi (i : ι) : (B i (f i (x i))).IsInvertible :=
    isInvertible_of_uniformEllipticity hb (hBlow i)
  obtain ⟨CA, hCA⟩ := hAj
  obtain ⟨CB, hCB⟩ := hBj
  have hfirst : ∃ C : ℝ, ∀ i, ‖fderiv ℝ (f i) (x i)‖ ≤ C := by
    refine ⟨Real.sqrt (max CA 0 / b), fun i => ?_⟩
    apply norm_le_of_pullback_quadratic_bounds (A i (x i)) (B i (f i (x i)))
      (fderiv ℝ (f i) (x i)) hb (le_max_right _ _)
      (fun v => ?_) (hBlow i) (fun u v => ((hmetric i).self_of_nhds u v).symm)
    have hnorm : ‖A i (x i)‖ ≤ max CA 0 :=
      (by simpa only [norm_iteratedFDeriv_zero] using hCA i 0 (Nat.zero_le r) :
        ‖A i (x i)‖ ≤ CA).trans (le_max_left _ _)
    calc
      A i (x i) v v ≤ ‖A i (x i) v v‖ := le_abs_self _
      _ ≤ ‖A i (x i)‖ * (‖v‖ * ‖v‖) := by
        simpa only [mul_assoc] using (A i (x i)).le_opNorm₂ v v
      _ ≤ max CA 0 * (‖v‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = max CA 0 * ‖v‖ ^ 2 := by rw [pow_two]
  obtain ⟨CΓA, _, hΓA⟩ := exists_finite_christoffel_jet_bound_at x hA₀ (r - 1)
    ⟨CA, fun i j hj => hCA i j (by omega)⟩ ha hAlow
  obtain ⟨CΓB, _, hΓB⟩ := exists_finite_christoffel_jet_bound_at (fun i => f i (x i))
    hB₀ (r - 1) ⟨CB, fun i j hj => hCB i j (by omega)⟩ hb hBlow
  obtain ⟨C, hC, hCj⟩ := exists_finite_transition_jet_bound_at x hf₀
    (fun i => CoordinateExponential.contDiffAt_christoffelBilinear (hA₀ i) (hAi i))
    (fun i => CoordinateExponential.contDiffAt_christoffelBilinear (hB₀ i) (hBi i))
    (r - 1) ⟨CΓA, hΓA⟩ ⟨CΓB, hΓB⟩ hzero hfirst
    (fun i => eventually_fderiv_fderiv_eq_of_metric_pullback (hf i) (hA i) (hB i)
      (hAi i) (hBi i) (hBsymm i) (hmetric i))
  exact ⟨C, hC, fun i j hj => hCj i j (by omega)⟩

end PoincareConjecture.CoordinateTransition
