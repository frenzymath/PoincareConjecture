import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence

set_option autoImplicit false
open Set Filter Poincare.Analysis.Calculus
open scoped ContDiff Topology

namespace PoincareConjecture.ChartDistance

theorem source_readout_smooth_convergence
    {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V)
    {τ σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hτ : ContDiffOn ℝ ∞ τ U) (hσ : ContDiffOn ℝ ∞ σ V)
    (hτV : MapsTo τ U V) (hinverse : EqOn (σ ∘ τ) id U)
    {f a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hflocal : ∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ x ∈ W ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hfjet : ∀ m K, IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
        (iteratedFDeriv ℝ m σ) atTop K)
    (hasmooth : ∀ᶠ k in atTop, ContDiff ℝ ∞ (a k))
    (hajet : ∀ m K, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
        (iteratedFDeriv ℝ m id) atTop K) :
    (∀ x ∈ U, ∃ W : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ (a k ∘ τ)) W) ∧
    ∀ m K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k ∘ (a k ∘ τ)))
        (iteratedFDeriv ℝ m id) atTop K := by
  have hinnerlocal : ∀ x ∈ U, ∃ W : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ x ∈ W ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k ∘ τ) W := by
    intro x hx
    exact ⟨U, hU, hx, hasmooth.mono fun _ hk => hk.comp_contDiffOn hτ⟩
  have hinnerjet : ∀ m K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k ∘ τ))
        (iteratedFDeriv ℝ m τ) atTop K := by
    intro m K hK hKU
    simpa only [Function.id_comp] using
      tendstoUniformlyOn_iteratedFDeriv_comp isOpen_univ hU
        contDiff_id.contDiffOn hτ (mapsTo_univ τ U)
        (fun x _ => ⟨univ, isOpen_univ, mem_univ x,
          hasmooth.mono fun _ hk => hk.contDiffOn⟩)
        (fun x hx => ⟨U, hU, hx, Eventually.of_forall fun _ => hτ⟩)
        (fun m K hK _ => hajet m K hK)
        (fun _ _ _ _ => Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
          Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε)
        m hK hKU
  have hinnerzero : ∀ K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => a k ∘ τ) τ atTop K := by
    intro K hK hKU
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
          (hinnerjet 0 K hK hKU)
  refine ⟨locally_eventually_smooth_comp hV hU hτ.continuousOn hτV
    hinnerzero hflocal hinnerlocal, ?_⟩
  intro m K hK hKU
  exact (tendstoUniformlyOn_iteratedFDeriv_comp hV hU hσ hτ hτV
    hflocal hinnerlocal hfjet hinnerjet m hK hKU).congr_right
      ((eqOn_iteratedFDeriv_of_isOpen hU hinverse m).mono hKU)

end PoincareConjecture.ChartDistance
