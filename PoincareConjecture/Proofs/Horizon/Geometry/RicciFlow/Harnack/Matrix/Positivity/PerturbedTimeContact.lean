import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedHeat
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedSpatialContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.TimeContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds.PrescribedJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

section Array

variable {I : Type*} [Fintype I] [DecidableEq I]

private lemma twoFormIdentity_input_action (C : I → I → ℝ)
    (hC : ∀ a b, C a b = C b a) (a b c d : I) :
    (∑ e, (C a e * twoFormIdentity e b c d + C b e * twoFormIdentity a e c d +
      C c e * twoFormIdentity a b e d + C d e * twoFormIdentity a b c e)) =
    C a c * (if b = d then 1 else 0) + C b d * (if a = c then 1 else 0) -
      C a d * (if b = c then 1 else 0) - C b c * (if a = d then 1 else 0) := by
  simp only [twoFormIdentity, sub_div, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_and, ite_div, zero_div, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  rw [hC c a, hC d b, hC d a, hC c b]
  split_ifs <;> ring

omit [Fintype I] in
private lemma delta_product_eq_twoFormIdentity (a b c d : I) :
    (((if a = c then 1 else 0 : ℝ) * (if b = d then 1 else 0) -
      (if a = d then 1 else 0) * (if b = c then 1 else 0)) / 2) =
      twoFormIdentity a b c d := by
  unfold twoFormIdentity
  split_ifs <;> simp_all

end Array

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma ricciTensorAction_metric_basis
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a c : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    D.ricciTensorAction (fun y z => g.inner y (z 0) (z 1)) x
      ![g.orthonormalBasis x a, g.orthonormalBasis x c] =
        2 * D.ricci x (g.orthonormalBasis x a) (g.orthonormalBasis x c) := by
  rw [D.ricciTensorAction_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, metric_inner_orthonormalBasis,
    mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [(hD.2.2.2.1 x (g.orthonormalBasis x c) (g.orthonormalBasis x a)
    (g.orthonormalBasis x c) (g.orthonormalBasis x a)).2.2.2]
  ring

lemma hasDerivAt_metricTwoFormIdentity_basis
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (a b c d : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    let E := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => metricTwoFormIdentity (F.metric s) x ![E a, E b, E c, E d])
      (-(F.connection t).ricciTensorAction (metricTwoFormIdentity (F.metric t)) x
        ![E a, E b, E c, E d]) t := by
  let E := (F.metric t).orthonormalBasis x
  let D := F.connection t
  have hg (i j) := (F.equation t (interior_subset ht) x (E i) (E j)).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have h := (((hg a c).mul (hg b d)).sub ((hg a d).mul (hg b c))).div_const 2
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hs (i j) : D.ricci x (E i) (E j) = D.ricci x (E j) (E i) :=
    (hD.2.2.2.1 x (E i) (E j) (E i) (E j)).2.2.2
  have ha := twoFormIdentity_input_action (fun i j => D.ricci x (E i) (E j)) hs a b c d
  convert h using 1 <;> try rfl
  dsimp only [E]
  simp only [LeviCivitaData.ricciTensorAction, Fin.sum_univ_four, metricTwoFormIdentity,
    Function.update_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    ← Finset.sum_add_distrib]
  simp only [metric_inner_orthonormalBasis, delta_product_eq_twoFormIdentity]
  dsimp only [D, E] at ha
  rw [ha]
  ring

noncomputable def perturbedHamiltonFixedQuadratic
    (F : RicciFlow n M J) (T₀ t : ℝ) (x : M) (α : ℝ → M → ℝ) (ψ : ℝ → ℝ)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) (s : ℝ) : ℝ :=
  let b := (F.metric t).orthonormalBasis x
  (∑ a, ∑ c, (hamiltonM (F.connection s) (s - T₀) x (b a) (b c) +
      α s x * (F.metric s).inner x (b a) (b c)) * W a * W c) +
    2 * (∑ a, ∑ c, ∑ d, hamiltonP (F.connection s) x (b a) (b c) (b d) * U a c * W d) +
    (∑ a, ∑ c, ∑ d, ∑ e,
      ((F.connection s).curvatureTensor x (b a) (b c) (b d) (b e) +
        ψ s * metricTwoFormIdentity (F.metric s) x ![b a, b c, b d, b e]) * U a c * U d e)

lemma perturbedHamiltonFixedQuadratic_self
    (F : RicciFlow n M J) (T₀ t : ℝ) (x : M) (α : ℝ → M → ℝ) (ψ : ℝ → ℝ)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a) :
    let b := (F.metric t).orthonormalBasis x
    perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W t =
      (∑ a, ∑ c, hamiltonM (F.connection t) (t - T₀) x (b a) (b c) * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d, hamiltonP (F.connection t) x (b a) (b c) (b d) * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e,
        (F.connection t).curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e) +
      α t x * (∑ a, W a ^ 2) + ψ t * (∑ a, ∑ c, (U a c) ^ 2) := by
  dsimp only [perturbedHamiltonFixedQuadratic]
  have hi := twoFormIdentity_quadratic U hU
  simp only [metric_inner_orthonormalBasis, metricTwoFormIdentity_orthonormalBasis,
    add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc, ← Finset.mul_sum]
  simp only [mul_assoc] at hi
  rw [hi]
  simp only [pow_two]
  ring

private lemma perturbed_ricci_action_zero
    (F : RicciFlow n M J) (T₀ t : ℝ) (x : M) (α : ℝ → M → ℝ) (ψ : ℝ → ℝ)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hQ : let b := (F.metric t).orthonormalBasis x
      (Matrix.fromBlocks
        (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
          (F.connection t).curvatureTensor x (b ac.1) (b ac.2) (b de.1) (b de.2) +
            ψ t * twoFormIdentity ac.1 ac.2 de.1 de.2)
        (fun ac d => hamiltonP (F.connection t) x (b ac.1) (b ac.2) (b d))
        (fun c de => hamiltonP (F.connection t) x (b de.1) (b de.2) (b c))
        (fun a c => hamiltonM (F.connection t) (t - T₀) x (b a) (b c) +
          α t x * (if a = c then 1 else 0))).PosSemidef)
    (hnull : perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W t = 0) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    (∑ a, ∑ c, D.ricciTensorAction (fun y z =>
      hamiltonM D (t - T₀) y (z 0) (z 1) + α t y * (F.metric t).inner y (z 0) (z 1))
        x ![b a, b c] * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d, D.ricciTensorAction
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![b a, b c, b d] * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e, D.ricciTensorAction
        (fun y z => D.riemannEvaluation y z + ψ t * metricTwoFormIdentity (F.metric t) y z)
        x ![b a, b c, b d, b e] * U a c * U d e) = 0 := by
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e) +
    ψ t * metricTwoFormIdentity (F.metric t) x ![b a, b c, b d, b e]
  let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
  let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c) +
    α t x * (F.metric t).inner x (b a) (b c)
  have hQ' : (Matrix.fromBlocks
      (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) => R ac.1 ac.2 de.1 de.2)
      (fun ac d => P ac.1 ac.2 d) (fun c de => P de.1 de.2 c) Q).PosSemidef := by
    simpa only [R, P, Q, b, D, metricTwoFormIdentity_orthonormalBasis,
      metric_inner_orthonormalBasis] using hQ
  have h := hamiltonBlock_input_action_zero R P Q U
    (fun a c => D.ricci x (b a) (b c)) W hQ' hnull
  dsimp only [R, P, Q, D, b] at h
  dsimp only
  simp only [LeviCivitaData.ricciTensorAction, Fin.sum_univ_two, Fin.sum_univ_three,
    Fin.sum_univ_four, Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    LeviCivitaData.riemannEvaluation, metricTwoFormIdentity, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, Finset.sum_add_distrib] at h ⊢
  exact h

private lemma ricciTensorAction_add_mul
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {r : ℕ}
    (A B : CovariantTensorEvaluation n M r) (f : M → ℝ) (x : M)
    (v : Fin r → TangentSpace (𝓡 n) x) :
    D.ricciTensorAction (fun y z => A y z + f y * B y z) x v =
      D.ricciTensorAction A x v + f x * D.ricciTensorAction B x v := by
  simp only [LeviCivitaData.ricciTensorAction, mul_add, Finset.sum_add_distrib]
  simp only [mul_left_comm, ← Finset.mul_sum]

private lemma deriv_perturbedHamiltonFixedQuadratic
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) (x : M)
    (α : ℝ → M → ℝ) (ψ : ℝ → ℝ)
    (hα : DifferentiableAt ℝ (fun s => α s x) t) (hψ : DifferentiableAt ℝ ψ t)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    deriv (perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W) t =
      (∑ a, ∑ c,
        (deriv (fun s => hamiltonM (F.connection s) (s - T₀) x (b a) (b c)) t -
          α t x * D.ricciTensorAction (fun y z => (F.metric t).inner y (z 0) (z 1))
            x ![b a, b c]) * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d,
        deriv (fun s => hamiltonP (F.connection s) x (b a) (b c) (b d)) t * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e,
        (deriv (fun s => (F.connection s).curvatureTensor x (b a) (b c) (b d) (b e)) t -
          ψ t * D.ricciTensorAction (metricTwoFormIdentity (F.metric t))
            x ![b a, b c, b d, b e]) * U a c * U d e) +
      deriv (fun s => α s x) t * (∑ a, W a ^ 2) +
      deriv ψ t * (∑ a, ∑ c, (U a c) ^ 2) := by
  let b := (F.metric t).orthonormalBasis x
  have hg (a c) : HasDerivAt (fun s => (F.metric s).inner x (b a) (b c))
      (-(F.connection t).ricciTensorAction
        (fun y z => (F.metric t).inner y (z 0) (z 1)) x ![b a, b c]) t := by
    rw [ricciTensorAction_metric_basis _ (hC.tensor_calculus n M _ _) x a c]
    convert (F.equation t (interior_subset ht) x (b a) (b c)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht) using 1 <;> try rfl
    ring
  have hM := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
      (((differentiableAt_hamiltonM hC F T₀ ht hτ x (b a) (b c)).hasDerivAt.add
        (hα.hasDerivAt.mul (hg a c))).mul_const (W a)).mul_const (W c)
  have hP := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun d _ => by
        have hp := (hasDerivAt_hamiltonP_evolution hC F ht x (b a) (b c) (b d)).differentiableAt.hasDerivAt
        exact (hp.mul_const (U a c)).mul_const (W d)
  have hR := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun e _ => by
          have hr := ((hC.curvature_evolution n M J F t (interior_subset ht) x
            (b a) (b c) (b d) (b e)).hasDerivAt
              (mem_interior_iff_mem_nhds.mp ht)).differentiableAt.hasDerivAt
          exact ((hr.add (hψ.hasDerivAt.mul
            (hasDerivAt_metricTwoFormIdentity_basis hC F ht x a c d e))).mul_const (U a c)).mul_const (U d e)
  have hd := ((hM.add (hP.const_mul 2)).add hR).deriv
  change deriv (perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W) t = _ at hd
  rw [hd]
  dsimp only
  have hi := twoFormIdentity_quadratic U hU
  simp only [b, metric_inner_orthonormalBasis, metricTwoFormIdentity_orthonormalBasis,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, mul_neg, neg_mul, Finset.sum_neg_distrib, mul_assoc,
    ← Finset.mul_sum] at hi ⊢
  rw [hi]
  simp only [pow_two]
  ring

lemma deriv_perturbedHamiltonFixedQuadratic_eq_heat_add_spatial
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) (x : M)
    (α : ℝ → M → ℝ) (ψ : ℝ → ℝ)
    (hα : DifferentiableAt ℝ (fun s => α s x) t) (hψ : DifferentiableAt ℝ ψ t)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a)
    (hQ : let b := (F.metric t).orthonormalBasis x
      (Matrix.fromBlocks
        (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
          (F.connection t).curvatureTensor x (b ac.1) (b ac.2) (b de.1) (b de.2) +
            ψ t * twoFormIdentity ac.1 ac.2 de.1 de.2)
        (fun ac d => hamiltonP (F.connection t) x (b ac.1) (b ac.2) (b d))
        (fun c de => hamiltonP (F.connection t) x (b de.1) (b de.2) (b c))
        (fun a c => hamiltonM (F.connection t) (t - T₀) x (b a) (b c) +
          α t x * (if a = c then 1 else 0))).PosSemidef)
    (hnull : perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W t = 0) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let Ric := fun a c => D.ricci x (b a) (b c)
    let k := (2 * (t - T₀))⁻¹
    let V := fun e a c =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W c -
        W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
    deriv (perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W) t =
      hamiltonHeatJetQuadratic F T₀ t x U W +
        hamiltonSpatialJetQuadratic D (t - T₀) x U W V +
        deriv (fun s => α s x) t * (∑ a, W a ^ 2) +
        deriv ψ t * (∑ a, ∑ c, (U a c) ^ 2) := by
  have hd := deriv_perturbedHamiltonFixedQuadratic hC F T₀ ht hτ x α ψ hα hψ U W hU
  have ha := perturbed_ricci_action_zero F T₀ t x α ψ U W hQ hnull
  dsimp only at hd ha ⊢
  simp only [ricciTensorAction_add_mul] at ha
  dsimp only [hamiltonHeatJetQuadratic, hamiltonSpatialJetQuadratic]
  simp only [RicciFlow.tensorHeatOperator, LeviCivitaData.riemannEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc] at hd ha ⊢
  linarith only [hd, ha]

theorem deriv_perturbedHamiltonFixedQuadratic_ge [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : 0 < t - T₀) (x : M)
    (α : ℝ → M → ℝ) (ψ : ℝ → ℝ)
    (hαtime : DifferentiableAt ℝ (fun s => α s x) t)
    (hψtime : DifferentiableAt ℝ ψ t)
    (hαspace : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (α t))
    (hα : 0 ≤ α t x) (hψ : 0 ≤ ψ t) (hψone : ψ t ≤ 1)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a)
    (hQ : ∀ᶠ y in 𝓝 x, let b := (F.metric t).orthonormalBasis y
      (Matrix.fromBlocks
        (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) =>
          (F.connection t).curvatureTensor y (b ac.1) (b ac.2) (b de.1) (b de.2) +
            ψ t * twoFormIdentity ac.1 ac.2 de.1 de.2)
        (fun ac d => hamiltonP (F.connection t) y (b ac.1) (b ac.2) (b d))
        (fun c de => hamiltonP (F.connection t) y (b de.1) (b de.2) (b c))
        (fun a c => hamiltonM (F.connection t) (t - T₀) y (b a) (b c) +
          α t y * (if a = c then 1 else 0))).PosSemidef)
    (hnull : perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W t = 0) :
    let D := F.connection t
    let k := (2 * (t - T₀))⁻¹
    let KR := D.curvatureDerivativeNorm 0 x
    let KP := 2 * n * D.curvatureDerivativeNorm 1 x
    let KM := 2 * (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x +
      3 * (n : ℝ) ^ 3 * KR ^ 2 + n * KR / (2 * (t - T₀))
    (deriv (fun s => α s x) t - D.laplacian (α t) x + 4 * k * α t x -
      2 * (n : ℝ) ^ 3 * (KR + 1) * α t x -
      (2 * (n : ℝ) ^ 3 * KM + 6 * (n : ℝ) ^ 4 * KP ^ 2 +
        4 * (n : ℝ) ^ 4 * KR ^ 2 + 4 * n * k ^ 2) * ψ t) * (∑ a, W a ^ 2) +
      (deriv ψ t - (6 * (n : ℝ) ^ 3 + 8 * (n : ℝ) ^ 4 * (2 * KR + 1)) * ψ t) *
        (∑ a, ∑ c, (U a c) ^ 2) ≤
      deriv (perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W) t := by
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let Ric := fun a c => D.ricci x (b a) (b c)
  let k := (2 * (t - T₀))⁻¹
  let V := fun e a c =>
    ((Ric e a + k * (if e = a then 1 else 0)) * W c -
      W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
  have hV (e a c) : V e a c = -V e c a := by dsimp only [V]; ring
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hn := hnull
  rw [perturbedHamiltonFixedQuadratic_self F T₀ t x α ψ U W hU] at hn
  have hd := deriv_perturbedHamiltonFixedQuadratic_eq_heat_add_spatial
    hC F T₀ ht (ne_of_gt hτ) x α ψ hαtime hψtime U W hU hQ.self_of_nhds hnull
  have hh := hamiltonHeatJetQuadratic_ge_perturbed_null_of_curvature
    hC F T₀ ht hτ x U W (α t x) (ψ t) hα hψ hψone hU hQ.self_of_nhds hn
  have hs := hamiltonSpatialJetQuadratic_nonneg_perturbed_null
    D hD (t - T₀) hαspace (ψ t) x hQ U W hU hn V hV
  have hj := neg_mul_sum_sq_geometric_prescribed_jet_ge D hD x
    (D.curvatureDerivativeNorm 0 x) k (ψ t) (Real.sqrt_nonneg _) le_rfl hψ W
  dsimp only [V, Ric, D, b, k] at hd hh hs hj ⊢
  linarith only [hd, hh, hs, hj]

def hamiltonPerturbationErrorBound (n : ℕ) (K T : ℝ) : ℝ :=
  1 + 2 * (n : ℝ) ^ 3 * (K + 1) +
    (6 * (n : ℝ) ^ 3 + 8 * (n : ℝ) ^ 4 * (2 * K + 1)) +
    (4 * (n : ℝ) ^ 5 * K + 30 * (n : ℝ) ^ 6 * K ^ 2 +
      4 * (n : ℝ) ^ 4 * K ^ 2) * T ^ 2 + (n : ℝ) ^ 4 * K * T + n

lemma hamiltonPerturbationErrorBound_pos {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) :
    0 < hamiltonPerturbationErrorBound n K T := by
  unfold hamiltonPerturbationErrorBound
  positivity

private lemma hamilton_error_coefficients_le
    (K T τ R P Q : ℝ) (hK : 0 ≤ K) (hτ : 0 < τ) (hT : τ ≤ T)
    (hR : 0 ≤ R) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hRK : R ≤ K) (hPK : P ≤ K) (hQK : Q ≤ K) :
    let C := hamiltonPerturbationErrorBound n K T
    2 * (n : ℝ) ^ 3 * (R + 1) ≤ C ∧
    6 * (n : ℝ) ^ 3 + 8 * (n : ℝ) ^ 4 * (2 * R + 1) ≤ C ∧
    2 * (n : ℝ) ^ 3 * (2 * (n : ℝ) ^ 2 * Q + 3 * (n : ℝ) ^ 3 * R ^ 2 +
      n * R / (2 * τ)) + 6 * (n : ℝ) ^ 4 * (2 * n * P) ^ 2 +
      4 * (n : ℝ) ^ 4 * R ^ 2 + 4 * n * ((2 * τ)⁻¹) ^ 2 ≤ C / τ ^ 2 := by
  let A := 2 * (n : ℝ) ^ 3 * (K + 1)
  let B := 6 * (n : ℝ) ^ 3 + 8 * (n : ℝ) ^ 4 * (2 * K + 1)
  let E := (4 * (n : ℝ) ^ 5 * K + 30 * (n : ℝ) ^ 6 * K ^ 2 +
    4 * (n : ℝ) ^ 4 * K ^ 2) * T ^ 2 + (n : ℝ) ^ 4 * K * T + n
  have hT₀ : 0 ≤ T := hτ.le.trans hT
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hCA : A ≤ hamiltonPerturbationErrorBound n K T := by
    change A ≤ 1 + A + B + _ + _ + _
    dsimp only [E] at hE
    linarith only [hB, hE]
  have hCB : B ≤ hamiltonPerturbationErrorBound n K T := by
    change B ≤ 1 + A + B + _ + _ + _
    dsimp only [E] at hE
    linarith only [hA, hE]
  have hCE : E ≤ hamiltonPerturbationErrorBound n K T := by
    change E ≤ 1 + A + B + _ + _ + _
    dsimp only [E]
    linarith only [hA, hB]
  refine ⟨le_trans ?_ hCA, le_trans ?_ hCB, ?_⟩
  · dsimp only [A]
    gcongr
  · dsimp only [B]
    gcongr
  · apply (le_div_iff₀ (sq_pos_of_pos hτ)).2
    calc
      _ = (4 * (n : ℝ) ^ 5 * Q + 6 * (n : ℝ) ^ 6 * R ^ 2 +
          24 * (n : ℝ) ^ 6 * P ^ 2 + 4 * (n : ℝ) ^ 4 * R ^ 2) * τ ^ 2 +
          (n : ℝ) ^ 4 * R * τ + n := by field_simp; ring
      _ ≤ (4 * (n : ℝ) ^ 5 * K + 6 * (n : ℝ) ^ 6 * K ^ 2 +
          24 * (n : ℝ) ^ 6 * K ^ 2 + 4 * (n : ℝ) ^ 4 * K ^ 2) * T ^ 2 +
          (n : ℝ) ^ 4 * K * T + n := by gcongr
      _ = E := by dsimp only [E]; ring
      _ ≤ _ := hCE

theorem deriv_perturbedHamiltonFixedQuadratic_ge_of_bound [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t K T : ℝ} (ht : t ∈ interior J) (hτ : 0 < t - T₀)
    (hT : t - T₀ ≤ T) (hK : 0 ≤ K) (x : M)
    (hbound : ∀ j ≤ 2, (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (α : ℝ → M → ℝ) (ψ : ℝ → ℝ)
    (hαtime : DifferentiableAt ℝ (fun s => α s x) t)
    (hψtime : DifferentiableAt ℝ ψ t)
    (hαspace : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (α t))
    (hα : 0 ≤ α t x) (hψ : 0 ≤ ψ t) (hψone : ψ t ≤ 1)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a)
    (hQ : ∀ᶠ y in 𝓝 x, let b := (F.metric t).orthonormalBasis y
      (Matrix.fromBlocks
        (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) =>
          (F.connection t).curvatureTensor y (b ac.1) (b ac.2) (b de.1) (b de.2) +
            ψ t * twoFormIdentity ac.1 ac.2 de.1 de.2)
        (fun ac d => hamiltonP (F.connection t) y (b ac.1) (b ac.2) (b d))
        (fun c de => hamiltonP (F.connection t) y (b de.1) (b de.2) (b c))
        (fun a c => hamiltonM (F.connection t) (t - T₀) y (b a) (b c) +
          α t y * (if a = c then 1 else 0))).PosSemidef)
    (hnull : perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W t = 0) :
    let C := hamiltonPerturbationErrorBound n K T
    (deriv (fun s => α s x) t - (F.connection t).laplacian (α t) x +
      2 / (t - T₀) * α t x - C * α t x - C * ψ t / (t - T₀) ^ 2) *
        (∑ a, W a ^ 2) +
      (deriv ψ t - C * ψ t) * (∑ a, ∑ c, (U a c) ^ 2) ≤
      deriv (perturbedHamiltonFixedQuadratic F T₀ t x α ψ U W) t := by
  have hc := hamilton_error_coefficients_le (n := n) K T (t - T₀)
    ((F.connection t).curvatureDerivativeNorm 0 x)
    ((F.connection t).curvatureDerivativeNorm 1 x)
    ((F.connection t).curvatureDerivativeNorm 2 x) hK hτ hT
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (hbound 0 (by omega)) (hbound 1 (by omega)) (hbound 2 (by omega))
  have hd := deriv_perturbedHamiltonFixedQuadratic_ge hC F T₀ ht hτ x α ψ
    hαtime hψtime hαspace hα hψ hψone U W hU hQ hnull
  dsimp only at hc hd ⊢
  refine le_trans (add_le_add
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun a _ => sq_nonneg (W a)))
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun c _ => sq_nonneg (U a c)))) hd
  · have ha := mul_le_mul_of_nonneg_right hc.1 hα
    have hp := mul_le_mul_of_nonneg_right hc.2.2 hψ
    have hk : 4 * (2 * (t - T₀))⁻¹ = 2 / (t - T₀) := by
      field_simp
      ring
    rw [hk]
    rw [div_mul_eq_mul_div] at hp
    linarith only [ha, hp]
  · exact sub_le_sub_left (mul_le_mul_of_nonneg_right hc.2.1 hψ) _

end Poincare.RicciFlow.Harnack
