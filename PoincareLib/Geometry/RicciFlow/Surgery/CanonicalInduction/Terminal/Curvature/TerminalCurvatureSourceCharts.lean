import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureOriginalCharts

/-!
# Original source maps on the fixed compact chart buffers

Compact exhaustion coverage supplies every chart-domain guard. The
inverse composite remains the literal original source map composition.
Source: derivations/terminal-curvature-compact-charts.md, Stage J4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- The same exhausting source embeddings eventually contain a compact
coordinate buffer, and the actual composite inverse is unchanged. -/
theorem terminalCurvature_source_chart_readout
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    {K : Set E} (hK : IsCompact K) (hKtarget : K ⊆ c.target) :
    (∀ k, (((phi k).symm.trans c).symm : E → M k) = phi k ∘ c.symm) ∧
      ∀ᶠ k in atTop, K ⊆ ((phi k).symm.trans c).target := by
  have hcompact : IsCompact (c.symm '' K) := hK.image_of_continuousOn
    (c.contMDiffOn_invFun.continuousOn.mono hKtarget)
  obtain ⟨j, hj⟩ := hcompact.elim_directed_cover U hU
    (by rw [hcover]; exact subset_univ _) hmono.directed_le
  refine ⟨fun _ => rfl, ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk x hx
  change x ∈ c.target ∧ c.symm x ∈ (phi k).source
  rw [hsource k]
  exact ⟨hKtarget hx, hmono hk (hj (mem_image_of_mem c.symm hx))⟩

end PoincareMT.M47
