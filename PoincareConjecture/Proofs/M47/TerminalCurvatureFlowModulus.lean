import PoincareConjecture.Proofs.M47.CanonicalNeckUniformTimeJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_metric_time_modulus
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {U : Set E} (hU : IsOpen U) (e : E → M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |s - t| < delta → ∀ x ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun y =>
          (F.metric s).pullbackCoefficients e y -
          (F.metric t).pullbackCoefficients e y) x‖ < rho := by
  exact Proofs.M47.metric_jets_uniform_time_delta_on_compact
    hab F hU he hK hKU m hrho

end PoincareConjecture.M47
