import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.InputAction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.BlockContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.QuadraticHeat
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Spacetime.M










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



lemma differentiableAt_hamiltonM
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0)
    (x : M) (a c : TangentSpace (𝓡 n) x) :
    DifferentiableAt ℝ (fun s => hamiltonM (F.connection s) (s - T₀) x a c) t := by
  let X := fun i : Fin 2 => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (![a, c] i)
  have hX (i : Fin 2) : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (X i)) x :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (![a, c] i)
  have h := contMDiffAt_hamiltonM_fields hC F T₀ ht hτ hX
  have hp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun s : ℝ => (s, x)) t := contMDiffAt_id.prodMk contMDiffAt_const
  have hd := ((h.comp t hp).contDiffAt.differentiableAt (by simp))
  simpa only [Function.comp_def, X, FiberBundle.extend_apply_self, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hd


lemma hamilton_ricci_action_zero_at_null
    {T₀ T₁ : ℝ} (F : RicciFlow n M (Set.Ioo T₀ T₁)) (t τ : ℝ) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hQ : HamiltonBlockPos F t x τ)
    (hnull : let D := F.connection t
      let b := (F.metric t).orthonormalBasis x
      (∑ a, ∑ c, hamiltonM D τ x (b a) (b c) * W a * W c) +
        2 * (∑ a, ∑ c, ∑ d, hamiltonP D x (b a) (b c) (b d) * U a c * W d) +
        (∑ a, ∑ c, ∑ d, ∑ e,
          D.curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e) = 0) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    (∑ a, ∑ c, D.ricciTensorAction (fun y z =>
      hamiltonM D τ y (z 0) (z 1)) x ![b a, b c] * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d,
        D.ricciTensorAction (fun y z => hamiltonP D y
          (z 0) (z 1) (z 2)) x ![b a, b c, b d] * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e,
        D.ricciTensorAction D.riemannEvaluation x ![b a, b c, b d, b e] * U a c * U d e) = 0 := by
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  have h := hamiltonBlock_input_action_zero
    (fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e))
    (fun a c d => hamiltonP D x (b a) (b c) (b d))
    (fun a c => hamiltonM D τ x (b a) (b c)) U
    (fun a c => D.ricci x (b a) (b c)) W hQ hnull
  dsimp only [D, b] at h
  dsimp only
  simp only [LeviCivitaData.ricciTensorAction, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Function.update_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    LeviCivitaData.riemannEvaluation]
  simp only [Finset.sum_add_distrib] at h
  exact h



theorem hamilton_time_quadratic_nonneg_at_null [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) {t : ℝ} (ht : t ∈ Set.Ioo T₀ T₁) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a)
    (hQ : ∀ᶠ y in 𝓝 x, HamiltonBlockPos F t y (t - T₀))
    (hnull : let D := F.connection t
      let b := (F.metric t).orthonormalBasis x
      (∑ a, ∑ c, hamiltonM D (t - T₀) x (b a) (b c) * W a * W c) +
        2 * (∑ a, ∑ c, ∑ d, hamiltonP D x (b a) (b c) (b d) * U a c * W d) +
        (∑ a, ∑ c, ∑ d, ∑ e,
          D.curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e) = 0) :
    let b := (F.metric t).orthonormalBasis x
    0 ≤ (∑ a, ∑ c,
      deriv (fun s => hamiltonM (F.connection s) (s - T₀) x (b a) (b c)) t * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d,
        deriv (fun s => hamiltonP (F.connection s) x (b a) (b c) (b d)) t * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e,
        deriv (fun s => (F.connection s).curvatureTensor x (b a) (b c) (b d) (b e)) t *
          U a c * U d e) := by
  classical
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let Ric := fun a c => D.ricci x (b a) (b c)
  let k := (2 * (t - T₀))⁻¹
  let V := fun e a c =>
    ((Ric e a + k * (if e = a then 1 else 0)) * W c -
      W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
  have hheat := hamilton_heat_quadratic_nonneg_at_null hC F ht x U W hU
    hQ.self_of_nhds hnull
  have hspace := hamilton_diffusion_quadratic_nonneg_at_null hC F t (t - T₀) x U W
    hQ hnull V
  have haction := hamilton_ricci_action_zero_at_null F t (t - T₀) x U W
    hQ.self_of_nhds hnull
  dsimp only [V, Ric, k, D, b] at hspace
  dsimp only at hheat hspace haction ⊢
  simp only [RicciFlow.tensorHeatOperator, LeviCivitaData.riemannEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc] at hheat hspace haction ⊢
  linarith only [hheat, hspace, haction]



theorem deriv_hamilton_quadratic_nonneg_at_null [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) {t : ℝ} (ht : t ∈ Set.Ioo T₀ T₁) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a)
    (hQ : ∀ᶠ y in 𝓝 x, HamiltonBlockPos F t y (t - T₀))
    (hnull : let D := F.connection t
      let b := (F.metric t).orthonormalBasis x
      (∑ a, ∑ c, hamiltonM D (t - T₀) x (b a) (b c) * W a * W c) +
        2 * (∑ a, ∑ c, ∑ d, hamiltonP D x (b a) (b c) (b d) * U a c * W d) +
        (∑ a, ∑ c, ∑ d, ∑ e,
          D.curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e) = 0) :
    let b := (F.metric t).orthonormalBasis x
    0 ≤ deriv (fun s =>
      (∑ a, ∑ c, hamiltonM (F.connection s) (s - T₀) x (b a) (b c) * W a * W c) +
        2 * (∑ a, ∑ c, ∑ d,
          hamiltonP (F.connection s) x (b a) (b c) (b d) * U a c * W d) +
        (∑ a, ∑ c, ∑ d, ∑ e,
          (F.connection s).curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e)) t := by
  classical
  let b := (F.metric t).orthonormalBasis x
  have ht' : t ∈ interior (Set.Ioo T₀ T₁) := by simpa only [interior_Ioo] using ht
  have hM := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
      (((differentiableAt_hamiltonM hC F T₀ ht' (ne_of_gt (sub_pos.mpr ht.1))
        x (b a) (b c)).hasDerivAt.mul_const (W a)).mul_const (W c))
  have hP := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun d _ => by
        have hd := (hasDerivAt_hamiltonP_evolution hC F ht' x (b a) (b c) (b d)).differentiableAt.hasDerivAt
        exact (hd.mul_const (U a c)).mul_const (W d)
  have hR := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun e _ => by
          have hd := ((hC.curvature_evolution n M (Set.Ioo T₀ T₁) F t ht x
            (b a) (b c) (b d) (b e)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht')).differentiableAt.hasDerivAt
          exact (hd.mul_const (U a c)).mul_const (U d e)
  dsimp only
  have hd := ((hM.add (hP.const_mul 2)).add hR).deriv
  simp only [Pi.add_def, b] at hd
  rw [hd]
  exact hamilton_time_quadratic_nonneg_at_null hC F ht x U W hU hQ hnull

end Poincare.RicciFlow.Harnack
