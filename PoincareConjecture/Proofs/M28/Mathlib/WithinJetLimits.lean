import PoincareConjecture.Proofs.M28.Mathlib.UniformLimitsWithin
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem exists_contDiffOn_of_locallyUniform_withinJet_limits
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hconv : Convex ℝ S) (hS : UniqueDiffOn ℝ S)
    (f : ℕ → E → F) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) S)
    (g : (m : ℕ) → E → E [×m]→L[ℝ] F)
    (hg : ∀ m, TendstoLocallyUniformlyOn
      (fun j => iteratedFDerivWithin ℝ m (f j) S) (g m) atTop S) :
    ∃ G : E → F, ContDiffOn ℝ ∞ G S ∧
      ∀ m, EqOn (iteratedFDerivWithin ℝ m G S) (g m) S := by
  have hcont (m : ℕ) : ContinuousOn (g m) S :=
    (hg m).continuousOn (Eventually.of_forall (fun j =>
      (hf j).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)) hS)).frequently
  have hderiv (m : ℕ) (x : E) (hx : x ∈ S) :
      HasFDerivWithinAt (g m)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F
          (g (m + 1) x)) S x := by
    apply hasFDerivWithinAt_of_tendstoLocallyUniformlyOn_convex hconv
      (l := atTop) (g := g m)
      (g' := fun y => continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) F (g (m + 1) y))
      (f := fun j => iteratedFDerivWithin ℝ m (f j) S)
      (f' := fun j x => continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) F (iteratedFDerivWithin ℝ (m + 1) (f j) S x))
    · intro j y hy
      exact ((hf j).differentiableOn_iteratedFDerivWithin
        (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
        hS y hy).hasFDerivWithinAt
    · exact fun y hy => (hg m).tendsto_at hy
    · exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) F).isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn
          (hg (m + 1))
    · exact hx
    · exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) F).continuous.continuousAt.comp_continuousWithinAt
          (hcont (m + 1) x hx)
  let G : E → F := fun x => continuousMultilinearCurryFin0 ℝ E F (g 0 x)
  have heq (m : ℕ) : EqOn (iteratedFDerivWithin ℝ m G S) (g m) S := by
    induction m with
    | zero =>
      intro x _
      simp [iteratedFDerivWithin_zero_eq_comp, G]
    | succ m ih =>
      intro x hx
      simp only [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
      rw [fderivWithin_congr ih (ih hx), (hderiv m x hx).fderivWithin (hS x hx)]
      exact LinearIsometryEquiv.symm_apply_apply _ _
  have hdiff (m : ℕ) : DifferentiableOn ℝ (iteratedFDerivWithin ℝ m G S) S :=
    (show DifferentiableOn ℝ (g m) S from
      fun x hx => (hderiv m x hx).differentiableWithinAt).congr (heq m)
  exact ⟨G, contDiffOn_of_continuousOn_differentiableOn
    (fun m _ => (hdiff m).continuousOn) (fun m _ => hdiff m), heq⟩
