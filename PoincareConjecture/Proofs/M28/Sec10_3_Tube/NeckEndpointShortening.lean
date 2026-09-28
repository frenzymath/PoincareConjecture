import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckShortening
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckExcursionSubarcs










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] {g : RiemannianMetric 3 M}




theorem exists_endpoint_neck_shortening (N : EpsilonNeck g)
    (hepsilon : N.epsilon ≤ neckShorteningEpsilon)
    {U : Set M} (hNU : N.central_sphere ⊆ U)
    {γ : ℝ → M} {a b c d t : ℝ}
    (hac : a ≤ c) (hct : c ≤ t) (htd : t ≤ d) (hdb : d ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hc : γ c ∈ N.central_sphere) (hd : γ d ∈ N.central_sphere)
    (hexcursion : γ t ∉ N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2)) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 + ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8) ≤
        g.pathELength γ a b := by
  obtain ⟨w, hcw, hwt, hprefix, hheight⟩ := N.exists_first_half_neck_subarc hct
    (hγ.continuousOn.mono (Icc_subset_Icc hac (htd.trans hdb))) hc hexcursion
  exact exists_neck_excursion_replacement N hepsilon hNU hac le_rfl hcw.le
    (hwt.trans htd) hdb hγ hγU hc hd hprefix hheight.ge

end PoincareConjecture.M28
