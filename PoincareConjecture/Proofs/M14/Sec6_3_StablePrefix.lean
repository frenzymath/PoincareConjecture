import PoincareConjecture.Proofs.M14.Sec6_3_PrefixNonconjugacy
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialPrefix
import PoincareConjecture.Proofs.M14.Sec6_3_StableDomain










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}



theorem exponentialPath_minimizing_of_uniqueBranch (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {b : ℝ} (hb : 0 < b) (hZ : (Z, b) ∈ E.domain)
    (hbranch : M14UniqueMinimizingBranch G T (b ^ 2) x E Z) :
    M14IsMinimizing (E.path Z b hZ hb) := by
  unfold M14UniqueMinimizingBranch at hbranch
  rw [Real.sqrt_sq hb.le] at hbranch
  obtain ⟨_, q, hcurve, hmin, _⟩ := hbranch
  apply (isMinimizing_iff_of_curve_eqOn (E.path Z b hZ hb) q ?_).mpr hmin
  intro t ht
  exact (E.path_coherent Z b hZ hb t (Ioo_subset_Icc_self ht)).trans
    (hcurve (Ioo_subset_Icc_self ht)).symm




theorem stableInitialVector_prefix
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {τ₀ τ : ℝ} {Z : G.Horizontal x}
    (hτ : 0 < τ) (hlt : τ < τ₀) (hstable : M14StableInitialVector G T τ₀ x E Z) :
    M14StableInitialVector G T τ x E Z := by
  obtain ⟨hZ₀, _, U, hU, hZU, hbranch⟩ := hstable
  have hτ₀ : 0 < τ₀ := hτ.trans hlt
  have hZ : (Z, Real.sqrt τ) ∈ E.domain :=
    (E.maximal_lifetime Z).out (E.domain_zero Z) hZ₀
      ⟨Real.sqrt_nonneg τ, Real.sqrt_le_sqrt hlt.le⟩
  have hc : Real.sqrt τ ∈ Ioo 0 (Real.sqrt τ₀) :=
    ⟨Real.sqrt_pos.mpr hτ, Real.sqrt_lt_sqrt hτ.le hlt⟩
  have hfull : M14UniqueMinimizingBranch G T ((Real.sqrt τ₀) ^ 2) x E Z := by
    simpa only [Real.sq_sqrt hτ₀.le] using hbranch Z hZU
  have hmin := exponentialPath_minimizing_of_uniqueBranch E (Real.sqrt_pos.mpr hτ₀) hZ₀ hfull
  refine ⟨hZ, exponential_prefix_differential_bijective hCoordinates hM04 hM12 E Z hZ₀ hc hmin hZ,
    U, hU, hZU, ?_⟩
  intro W hW
  exact uniqueMinimizingBranch_prefix hM04 hCoordinates hM12 E hτ hlt (hbranch W hW)

end PoincareConjecture.M14
