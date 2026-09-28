import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.JetBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.Proofs.M28.FiniteHessian

variable {ι β E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]



theorem HasUniformJetBoundsAt.add {n : ℕ} {f g : ι → E → F} {x : ι → E}
    (hf : HasUniformJetBoundsAt n f x) (hg : HasUniformJetBoundsAt n g x)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) :
    HasUniformJetBoundsAt n (fun i y => f i y + g i y) x := by
  intro m hm
  obtain ⟨C, hC⟩ := hf m hm
  obtain ⟨D, hD⟩ := hg m hm
  refine ⟨C + D, fun i => ?_⟩
  change ‖iteratedFDeriv ℝ m (f i + g i) (x i)‖ ≤ C + D
  rw [iteratedFDeriv_add_apply
    ((hcf i).of_le (by exact_mod_cast le_top))
    ((hcg i).of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hC i) (hD i))



theorem HasUniformJetBoundsAt.sum [Fintype β]
    {n : ℕ} {f : β → ι → E → F} {x : ι → E}
    (hf : ∀ b, HasUniformJetBoundsAt n (f b) x)
    (hc : ∀ i b, ContDiffAt ℝ ∞ (f b i) (x i)) :
    HasUniformJetBoundsAt n (fun i p => ∑ b, f b i p) x := by
  classical
  intro j hj
  choose C hC using fun b => hf b j hj
  refine ⟨∑ b, C b, fun i => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun b _ =>
    (hc i b).of_le (by exact_mod_cast le_top))]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ => hC b i))




theorem HasUniformJetBoundsAt.of_basis [Finite β] [FiniteDimensional ℝ F]
    (b : Module.Basis β ℝ F) {n : ℕ} {f : ι → E → F →L[ℝ] G} {x : ι → E}
    (hf : ∀ a, HasUniformJetBoundsAt n (fun i p => f i p (b a)) x)
    (hc : ∀ i a, ContDiffAt ℝ ∞ (fun p => f i p (b a)) (x i)) :
    HasUniformJetBoundsAt n f x := by
  classical
  let : Fintype β := Fintype.ofFinite β
  let L (a : β) : G →L[ℝ] F →L[ℝ] G :=
    ContinuousLinearMap.smulRightL ℝ F G (b.coord a).toContinuousLinearMap
  have hsum := HasUniformJetBoundsAt.sum
    (fun a => (hf a).clm (fun i => hc i a) (L a))
    (fun i a => (L a).contDiff.contDiffAt.comp (x i) (hc i a))
  apply hsum.congr_germ
  intro i
  apply Filter.Eventually.of_forall
  intro p
  ext v
  change (ContinuousLinearMap.apply ℝ G v) (∑ a, L a (f i p (b a))) = f i p v
  rw [map_sum]
  change (∑ a, b.repr v a • f i p (b a)) = f i p v
  simpa only [map_sum, map_smul] using congrArg (f i p) (b.sum_repr v)

end PoincareConjecture.Proofs.M28.FiniteHessian
