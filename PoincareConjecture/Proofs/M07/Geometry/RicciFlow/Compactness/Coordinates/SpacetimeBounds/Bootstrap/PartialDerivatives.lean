import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.UniformBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SpacetimeBounds.Bootstrap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def timeLift : V →L[ℝ] (ℝ × E →L[ℝ] V) :=
  ContinuousLinearMap.smulRightL ℝ (ℝ × E) V (ContinuousLinearMap.fst ℝ ℝ E)

noncomputable def spaceLift : (E →L[ℝ] V) →L[ℝ] (ℝ × E →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ (ℝ × E) E V).flip (ContinuousLinearMap.snd ℝ ℝ E)

theorem fderiv_eq_partials {f : ℝ × E → V} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ f z = timeLift (E := E) (deriv (fun t => f (t, z.2)) z.1) +
      spaceLift (fderiv ℝ (fun x => f (z.1, x)) z.2) := by
  have ht := (hf.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  have hx := (hf.hasFDerivAt.comp z.2
    ((hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2))).fderiv
  dsimp only [Function.comp_def, id_eq] at ht hx
  apply ContinuousLinearMap.ext
  intro v
  rw [ht, hx]
  change fderiv ℝ f z v = v.1 • fderiv ℝ f z (1, 0) + fderiv ℝ f z (0, v.2)
  rw [← map_smul, ← map_add]
  congr 1
  ext <;> simp

theorem norm_iteratedFDeriv_succ_le_partials {f : ℝ × E → V}
    {J : Set ℝ} {U : Set E} (hf : ContDiffOn ℝ ∞ f (J ×ˢ U))
    (hJ : IsOpen J) (hU : IsOpen U) {z : ℝ × E} (hz : z ∈ J ×ˢ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ (m + 1) f z‖ ≤
      ‖timeLift (E := E) (V := V)‖ *
        ‖iteratedFDeriv ℝ m (fun w : ℝ × E => deriv (fun t => f (t, w.2)) w.1) z‖ +
      ‖spaceLift (E := E) (V := V)‖ *
        ‖iteratedFDeriv ℝ m (fun w : ℝ × E => fderiv ℝ (fun x => f (w.1, x)) w.2) z‖ := by
  have ht := (SpacetimeBounds.contDiffOn_timeDeriv hf hJ hU).contDiffAt
    ((hJ.prod hU).mem_nhds hz)
  have hx := (SpacetimeBounds.contDiffOn_spatialFDeriv hf hJ hU).contDiffAt
    ((hJ.prod hU).mem_nhds hz)
  have heq : fderiv ℝ f =ᶠ[𝓝 z] (fun w : ℝ × E =>
      timeLift (E := E) (deriv (fun t => f (t, w.2)) w.1) +
      spaceLift (fderiv ℝ (fun x => f (w.1, x)) w.2)) := by
    filter_upwards [(hJ.prod hU).mem_nhds hz] with w hw
    exact fderiv_eq_partials ((hf.contDiffAt ((hJ.prod hU).mem_nhds hw)).differentiableAt
      (by simp))
  rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  have hadd := fun_iteratedFDeriv_add_apply
    (((timeLift (E := E) (V := V)).contDiff.contDiffAt.comp z ht).of_le
      (show (m : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))
    (((spaceLift (E := E) (V := V)).contDiff.contDiffAt.comp z hx).of_le
      (show (m : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))
  dsimp only [Function.comp_def] at hadd
  rw [hadd]
  apply (norm_add_le _ _).trans
  exact add_le_add
    ((timeLift (E := E) (V := V)).norm_iteratedFDeriv_comp_left ht (by exact_mod_cast le_top))
    ((spaceLift (E := E) (V := V)).norm_iteratedFDeriv_comp_left hx (by exact_mod_cast le_top))

theorem EventuallyBoundedJet.succ_of_partials {α : Type*} {l : Filter α}
    {f : α → ℝ × E → V} {J : α → Set ℝ} {U : α → Set E} {S : α → Set (ℝ × E)}
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (J a ×ˢ U a))
    (hJ : ∀ a, IsOpen (J a)) (hU : ∀ a, IsOpen (U a))
    (hS : ∀ a, S a ⊆ J a ×ˢ U a) {m : ℕ}
    (ht : EventuallyBoundedJet l S
      (fun a z => deriv (fun t => f a (t, z.2)) z.1) m)
    (hx : EventuallyBoundedJet l S
      (fun a z => fderiv ℝ (fun x => f a (z.1, x)) z.2) m) :
    EventuallyBoundedJet l S f (m + 1) := by
  obtain ⟨Bt, hBt, ht⟩ := ht
  obtain ⟨Bx, hBx, hx⟩ := hx
  refine ⟨‖timeLift (E := E) (V := V)‖ * Bt +
    ‖spaceLift (E := E) (V := V)‖ * Bx, by positivity, ?_⟩
  filter_upwards [ht, hx] with a hat hax z hz
  exact (norm_iteratedFDeriv_succ_le_partials (hf a) (hJ a) (hU a) (hS a hz) m).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hat z hz) (norm_nonneg (timeLift (E := E) (V := V))))
      (mul_le_mul_of_nonneg_left (hax z hz) (norm_nonneg (spaceLift (E := E) (V := V)))))

end PoincareConjecture.SpacetimeBounds.Bootstrap
