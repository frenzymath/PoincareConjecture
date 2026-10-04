import Mathlib.Topology.MetricSpace.Thickening

/-!
# A common target-chart margin for compact source patches

The finite-chart construction in the SurgeryComparison.Transport full contract, following
Morgan--Tian Claim 18.22, printed p. 433, fixes the chart data before
choosing successive smoothing parameters. Compact image thickenings
provide one positive distance margin valid for every nearby map.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ENNReal

universe uM uN uI

namespace PoincareMT.SurgeryComparison.Topology

variable {M : Type uM} [TopologicalSpace M]
  {N : Type uN} [PseudoEMetricSpace N]
  {ι : Type uI} [Finite ι]

/-- One positive uniform distance margin keeps the images of finitely
many compact source sets inside their prescribed open target sets. The
perturbed map need not be continuous. This is the fixed-chart validity
step in the SurgeryComparison.Transport full contract, Claim 18.22, Morgan--Tian p. 433. -/
theorem exists_pos_uniform_mapsTo_of_edist_lt
    (K : ι → Set M) (V : ι → Set N) (f₀ : M → N)
    (hK : ∀ i, IsCompact (K i)) (hV : ∀ i, IsOpen (V i))
    (hf₀ : ∀ i, ContinuousOn f₀ (K i))
    (hmap : ∀ i, MapsTo f₀ (K i) (V i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : M → N,
      (∀ x, edist (f x) (f₀ x) < ENNReal.ofReal δ) →
      ∀ i, MapsTo f (K i) (V i) := by
  classical
  have hradii : ∀ i, ∃ r : ℝ, 0 < r ∧ thickening r (f₀ '' K i) ⊆ V i :=
    fun i => ((hK i).image_of_continuousOn (hf₀ i)).exists_thickening_subset_open
      (hV i) (hmap i).image_subset
  choose r hr hrange using hradii
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i, δ < r i :=
    eventually_all.mpr (fun i => eventually_lt_nhds (hr i))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hsmall' : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i, δ < r i :=
    nhdsWithin_le_nhds hsmall
  obtain ⟨δ, hδ, hδr⟩ := (hpos.and hsmall').exists
  refine ⟨δ, hδ, ?_⟩
  intro f hf i x hx
  apply hrange i
  exact (mem_thickening_iff_exists_edist_lt _ _).mpr
    ⟨f₀ x, mem_image_of_mem f₀ hx,
      (hf x).trans_le (ENNReal.ofReal_le_ofReal (hδr i).le)⟩

end PoincareMT.SurgeryComparison.Topology
