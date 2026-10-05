import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Neck.CanonicalNeckUniformTimeJets

/-!
# Actual closed-flow time moduli on compact source charts

The modulus is produced by the given closed Ricci flow and its actual
chart map. It is local to one compact buffer and one finite derivative
order; no common source lifetime is introduced.
Source: derivations/terminal-curvature-earlier-slices.md, L1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- A literal closed ordinary flow supplies one uniform time modulus for
all metric coefficient jets on one compact chart buffer. -/
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

end PoincareMT.M47
