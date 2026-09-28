import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound
import PoincareConjecture.Proofs.M34.Mathlib.NeckCylinderChartBounds

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

section Local

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem smooth_germ_iteratedFDeriv {f : E → F} {x : E}
    (hf : ContDiffAt 𝕜 ∞ f x) (m : ℕ) :
    ContDiffAt 𝕜 ∞ (iteratedFDeriv 𝕜 m f) x := by
  induction m with
  | zero =>
    let e := (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv
    exact e.toContinuousLinearMap.contDiff.contDiffAt.comp x hf
  | succ m ih =>
    let e := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => E) F).symm
    convert! e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp x
      (ih.fderiv_right (m := ∞) (by simp)) using 1

theorem ContDiffAt.exists_eventually_finite_jet_bound {f : E → F} {x : E}
    (hf : ContDiffAt 𝕜 ∞ f x) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ y in 𝓝 x, ∀ j ≤ N,
      ‖iteratedFDeriv 𝕜 j f y‖ ≤ C := by
  let B : Fin (N + 1) → ℝ := fun j => ‖iteratedFDeriv 𝕜 j f x‖ + 1
  have hB (j : Fin (N + 1)) : 0 ≤ B j := by dsimp [B]; positivity
  have hlocal (j : Fin (N + 1)) :
      ∀ᶠ y in 𝓝 x, ‖iteratedFDeriv 𝕜 j f y‖ ≤ B j := by
    have hc := (smooth_germ_iteratedFDeriv hf j).continuousAt.norm
    filter_upwards [hc.tendsto.eventually
      (isOpen_Iio.mem_nhds (lt_add_one ‖iteratedFDeriv 𝕜 j f x‖))] with y hy
    exact hy.le
  refine ⟨1 + ∑ j : Fin (N + 1), B j, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hB j)
  · have hall : ∀ᶠ y in 𝓝 x, ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))),
        ‖iteratedFDeriv 𝕜 j f y‖ ≤ B j :=
      (Finset.univ : Finset (Fin (N + 1))).eventually_all.mpr (fun j _ => hlocal j)
    filter_upwards [hall] with y hy j hj
    let l : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hy l (Finset.mem_univ l)).trans ((Finset.single_le_sum
      (fun i _ => hB i) (Finset.mem_univ l)).trans (le_add_of_nonneg_left zero_le_one))

end Local

section Composition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_composition_finite_jet_bound (N : ℕ) {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : E → F) (g : F → G) (x : E),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g (f x) →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j f x‖ ≤ B) →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A) →
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ C := by
  refine ⟨max 1 (N.factorial * A * B ^ N), le_max_left _ _, ?_⟩
  intro f g x hf hg hfj hgj j hj
  have h := norm_iteratedFDeriv_comp_le_of_contDiffAt hf hg j
    (fun l hl => hgj l (hl.trans hj))
    (fun l hl hlm => (hfj l (hlm.trans hj)).trans
      (le_self_pow₀ hB (Nat.ne_of_gt hl)))
  apply h.trans
  apply le_trans _ (le_max_right _ _)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
      (zero_le_one.trans hA))
    (pow_le_pow_right₀ hB hj) (pow_nonneg (zero_le_one.trans hB) _) (by positivity)

end Composition

theorem contDiff_included_sphereCylinder_chart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (q : Metric.sphere (0 : E) 1) :
    ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      (((chartAt (EuclideanSpace ℝ (Fin n)) q).symm p.1 : E), p.2)) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞
      (fun y => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y : E)) :=
    contMDiff_coe_sphere.comp (contMDiff_sphere_chart_symm q)
  exact ((contMDiff_iff_contDiff.mp h).comp contDiff_fst).prodMk contDiff_snd
