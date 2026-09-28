import PoincareConjecture.Proofs.M60.Mathlib.HarmonicBranchIsolation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.DiscreteSubset














set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

universe u

namespace PoincareConjecture

local notation "E" => EuclideanSpace ℝ (Fin 2)



def m64PlaneDifferentialZeroSet
    {n : ℕ} (u : ℂ → EuclideanSpace ℝ (Fin n)) : Set ℂ :=
  {z | fderiv ℝ u z = 0}





theorem m64PlaneHarmonicDifferential_zeroSet_finite
    {n : ℕ} {Γ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)}
    {u : ℂ → EuclideanSpace ℝ (Fin n)} {O : Set ℂ}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hΓ : ∀ z ∈ O, ContDiffAt ℝ 1 Γ (u z))
    (hsym : ∀ z ∈ O, ∀ a b : EuclideanSpace ℝ (Fin n),
      Γ (u z) a b = Γ (u z) b a)
    (hτ : ∀ z ∈ O,
      ConnectionVariation.covDerivAlong Γ u
          (fun w => fderiv ℝ u w 1) 1 z +
        ConnectionVariation.covDerivAlong Γ u
          (fun w => fderiv ℝ u w Complex.I) Complex.I z = 0)
    {K : Set ℂ} (hK : IsCompact (m64PlaneDifferentialZeroSet u ∩ K))
    (hKO : K ⊆ O)
    (hnot_open : ∀ z ∈ m64PlaneDifferentialZeroSet u ∩ K,
      ¬ m64PlaneDifferentialZeroSet u ∈ 𝓝 z) :
    (m64PlaneDifferentialZeroSet u ∩ K).Finite := by
  apply hK.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro z hz
  have hzO : z ∈ O := hKO hz.2
  rcases M60.harmonic_differential_eventually_zero_or_isolated
      hO hu hΓ hsym hτ hzO with hall | hisol
  · exact False.elim (hnot_open z hz hall)
  · change ∀ᶠ w in 𝓝[≠] z, w ∉ m64PlaneDifferentialZeroSet u at hisol
    rw [eventually_nhdsWithin_iff] at hisol
    change {w : ℂ | w ∈ ({z} : Set ℂ)ᶜ →
      w ∉ m64PlaneDifferentialZeroSet u} ∈ 𝓝 z at hisol
    obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hisol
    refine ⟨U, hUopen, ?_⟩
    ext y
    constructor
    · intro hy
      by_cases hyz : y = z
      · exact Set.mem_singleton_iff.mpr hyz
      · exfalso
        exact (hUsub hy.1) hyz hy.2.1
    · intro hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨hzU, hz⟩

end PoincareConjecture
