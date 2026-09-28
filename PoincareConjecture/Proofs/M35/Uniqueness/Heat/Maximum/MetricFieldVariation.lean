import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricTaylorRemainder
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricTimePotential
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricFormTest









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem scalarFieldsLp_inner (u v : PiLp 2 (fun _ : Fin m => L2)) :
    inner ℝ (scalarFieldsLp u) (scalarFieldsLp v) = inner ℝ u v := by
  rw [L2.inner_def, PiLp.inner_apply]
  simp only [L2.inner_def]
  rw [← integral_finsetSum _ (fun j _ => L2.integrable_inner (𝕜 := ℝ) (u j) (v j))]
  apply integral_congr_ae
  filter_upwards [scalarFieldsLp_coe u, scalarFieldsLp_coe v] with x hu hv
  rw [hu, hv, PiLp.inner_apply]

theorem dirichletFieldValue_inner (K : Set V)
    (u v : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    inner ℝ (dirichletFieldValue K u) (dirichletFieldValue K v) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) u)
        (finiteHilbertMap (dirichletInclusion K) v) := by
  change inner ℝ
    (scalarFieldsLp (finiteHilbertMap ((dirichletValue K).subtypeL.comp (dirichletInclusion K)) u))
    (scalarFieldsLp
      (finiteHilbertMap ((dirichletValue K).subtypeL.comp (dirichletInclusion K)) v)) = _
  let U : PiLp 2 (fun _ : Fin m => L2) :=
    finiteHilbertMap ((dirichletValue K).subtypeL.comp (dirichletInclusion K)) u
  let W : PiLp 2 (fun _ : Fin m => L2) :=
    finiteHilbertMap ((dirichletValue K).subtypeL.comp (dirichletInclusion K)) v
  exact (scalarFieldsLp_inner U W).trans rfl

theorem metric_form_test_pointwise_pair {K : Set V}
    (g : RiemannianMetric n V) (η : V → ℝ) (Q : ℝ)
    (u z : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hz : ∀ j : Fin n, (dirichletInclusion K (z j) : L2) =ᵐ[volume]
      fun x => metricEntropyTest g η Q (EuclideanSpace.single j 1)
        (x, dirichletFieldValue K u x)) :
    ∀ᵐ x ∂volume, ∀ w : V, inner ℝ (dirichletFieldValue K z x) w =
      fderiv ℝ (fun v => metricEntropyPotential g η Q (x, v))
        (dirichletFieldValue K u x) w := by
  let Z : PiLp 2 (fun _ : Fin n => L2) :=
    finiteHilbertMap ((dirichletValue K).subtypeL.comp (dirichletInclusion K)) z
  have hv := scalarFieldsLp_coe Z
  change dirichletFieldValue K z =ᵐ[volume] _ at hv
  filter_upwards [hv, ae_all_iff.mpr hz] with x hx hz
  intro w
  rw [hx, PiLp.inner_apply,
    (metricEntropyPotential_value_hasFDerivAt g η Q x (dirichletFieldValue K u x)).fderiv]
  change (∑ j, inner ℝ ((dirichletInclusion K (z j) : L2) x) (w j)) = _
  simp only [hz, RCLike.inner_apply, conj_trivial]
  convert! metricEntropy_test_pair g η Q x (dirichletFieldValue K u x) w using 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _



theorem metric_form_test_hasFDerivAt {K : Set V}
    (g : RiemannianMetric n V) (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q)
    (u z : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hz : ∀ j : Fin n, (dirichletInclusion K (z j) : L2) =ᵐ[volume]
      fun x => metricEntropyTest g η Q (EuclideanSpace.single j 1)
        (x, dirichletFieldValue K u x)) :
    HasFDerivAt (fieldIntegral (metricEntropyPotential g η Q))
      (innerSL ℝ (dirichletFieldValue K z)) (dirichletFieldValue K u) := by
  refine (metricEntropyPotential_quadratic_remainder g hη hc Q).elim ?_
  intro C hC
  apply fieldIntegral_hasFDerivAt _ (metricEntropyPotential_integrable g hη hc hQ)
    (dirichletFieldValue K u) (dirichletFieldValue K z) (C := C)
  intro v
  filter_upwards [metric_form_test_pointwise_pair g η Q u z hz] with x hx
  rw [hx]
  exact hC.2 x (dirichletFieldValue K u x) (v x)

end PoincareConjecture.M35.Uniqueness.Heat
