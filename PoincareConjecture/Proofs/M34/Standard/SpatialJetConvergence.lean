import PoincareConjecture.Proofs.M07.Analysis.Calculus.SpatialJets
import Mathlib.Topology.UniformSpace.UniformConvergence










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M34



theorem tendstoUniformlyOn_spatialJets_of_jointJets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℕ → ℝ × E → F} {g : ℝ × E → F} {K : Set (ℝ × E)} (m : ℕ)
    (hf : ∀ᶠ k : ℕ in atTop, ∀ p ∈ K, ContDiffAt ℝ ∞ (f k) p)
    (hg : ∀ p ∈ K, ContDiffAt ℝ ∞ g p)
    (hconv : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m g) atTop K) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (fun x => f k (p.1, x)) p.2)
      (fun p => iteratedFDeriv ℝ m (fun x => g (p.1, x)) p.2) atTop K := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := F) (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E)
  have h := P.uniformContinuous.comp_tendstoUniformlyOn hconv
  have hlim : EqOn (fun p => P (iteratedFDeriv ℝ m g p))
      (fun p => iteratedFDeriv ℝ m (fun x => g (p.1, x)) p.2) K := by
    intro p hp
    ext v
    exact (Poincare.Analysis.iteratedFDeriv_spatial_slice g (hg p hp) m v).symm
  apply (h.congr_right hlim).congr
  filter_upwards [hf] with k hk p hp
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice (f k) (hk p hp) m v).symm

end PoincareConjecture.M34
