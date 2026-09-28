import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.RawMetricMaximum








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem dirichletValueField_inner (K : Set V)
    (u v : PiLp 2 (fun _ : Fin m => dirichletValue K)) :
    inner ℝ (dirichletValueField K u) (dirichletValueField K v) = inner ℝ u v := by
  change inner ℝ (scalarFieldsLp (finiteHilbertMap (dirichletValue K).subtypeL u))
    (scalarFieldsLp (finiteHilbertMap (dirichletValue K).subtypeL v)) = _
  exact (scalarFieldsLp_inner _ _).trans rfl

theorem dirichletValueField_test (K : Set V) (f : Fin m → supportedTests K) :
    dirichletValueField K (vectorTestValue K f) =
      (schwartzField (fun j => (f j : 𝓢(V, ℝ)))).toLp 2 volume :=
  (schwartzField_toLp _).symm

theorem vectorTestValue_pair_integral (K : Set V) (f : Fin m → supportedTests K)
    (u : PiLp 2 (fun _ : Fin m => dirichletValue K)) :
    inner ℝ (vectorTestValue K f) u =
      ∫ x, inner ℝ (schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)
        (dirichletValueField K u x) := by
  rw [← dirichletValueField_inner, dirichletValueField_test, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(schwartzField (fun j => (f j : 𝓢(V, ℝ)))).coeFn_toLp 2 volume]
    with x hx
  rw [hx]

theorem vectorTestValue_pair_bound (K : Set V) (f : Fin m → supportedTests K)
    (u : PiLp 2 (fun _ : Fin m => dirichletValue K)) {E : Set V} (hE : IsCompact E)
    {M N : ℝ}
    (hf0 : ∀ x ∉ E, schwartzField (fun j => (f j : 𝓢(V, ℝ))) x = 0)
    (hf : ∀ x ∈ E, ‖schwartzField (fun j => (f j : 𝓢(V, ℝ))) x‖ ≤ M)
    (hu : ∀ᵐ x ∂volume, x ∈ E → ‖dirichletValueField K u x‖ ≤ N) :
    ‖inner ℝ (vectorTestValue K f) u‖ ≤ (M * N) * volume.real E := by
  rw [vectorTestValue_pair_integral]
  have hs : (∫ x in E, inner ℝ (schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)
      (dirichletValueField K u x)) =
      ∫ x, inner ℝ (schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)
        (dirichletValueField K u x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hf0 x hx, inner_zero_left])
  rw [← hs]
  apply norm_setIntegral_le_of_norm_le_const_ae' hE.measure_lt_top
  filter_upwards [hu] with x hx
  intro hxE
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul (hf x hxE) (hx hxE) (norm_nonneg _) ((norm_nonneg _).trans (hf x hxE)))

theorem metric_bound_euclidean_bound (g : RiemannianMetric n V) {E : Set V}
    {c Q : ℝ} (hc : 0 < c) (hQ : 0 ≤ Q)
    (hlower : ∀ x ∈ E, ∀ z : V, c * ‖z‖ ^ 2 ≤ g.inner x z z)
    {u : V → V} (hu : ∀ᵐ x ∂volume, x ∈ E → g.inner x (u x) (u x) ≤ Q) :
    ∀ᵐ x ∂volume, x ∈ E → ‖u x‖ ≤ 1 + Q / c := by
  filter_upwards [hu] with x hx
  intro hxE
  have hsq : ‖u x‖ ^ 2 ≤ Q / c :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using (hlower x hxE (u x)).trans (hx hxE))
  have hdiv : 0 ≤ Q / c := div_nonneg hQ hc.le
  nlinarith [sq_nonneg (‖u x‖ - 1)]

end PoincareConjecture.M35.Uniqueness.Heat
