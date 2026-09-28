import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Uniqueness
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SingularRegularLimit



theorem smooth_limit_of_eventual_jet_bounds
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ι → EuclideanSpace ℝ (Fin n) → V}
    {g : EuclideanSpace ℝ (Fin n) → V}
    (hpoint : ∀ x ∈ U, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hsmooth : ∀ᶠ i in l, ContDiffOn ℝ ∞ (f i) U)
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ i in l, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ B) :
    ContDiffOn ℝ ∞ g U ∧
      ∀ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → K ⊆ U →
        TendstoUniformlyOn (fun i => iteratedFDeriv ℝ m (f i))
          (iteratedFDeriv ℝ m g) l K := by
  have hseq (σ : ℕ → ι) (hσ : Tendsto σ atTop l) :
      Poincare.Analysis.Calculus.LocallyEventuallyBoundedDerivatives U
        (fun k => f (σ k)) := by
    intro K hK hKU m
    obtain ⟨B, hB⟩ := hbound K hK hKU m
    exact ⟨B, hσ.eventually hB⟩
  constructor
  · obtain ⟨σ, hσ⟩ := l.exists_seq_tendsto
    exact Poincare.Analysis.Calculus.contDiffOn_of_locally_eventually_smooth
      (fun x hx => (hpoint x hx).comp hσ)
      (fun x hx => ⟨U, hU, hx, Subset.rfl, hσ.eventually hsmooth⟩) (hseq σ hσ)
  · intro m K hK hKU
    apply tendstoUniformlyOn_iff_seq_tendstoUniformlyOn.mpr
    intro σ hσ
    exact Poincare.Analysis.Calculus.tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth hU
      (fun x hx => (hpoint x hx).comp hσ) (hσ.eventually hsmooth) (hseq σ hσ) m hK hKU

end PoincareConjecture.SingularRegularLimit
