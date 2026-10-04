import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Joining.GaugeJoin

/-!
# Regularity across the two gauge-join patch boundaries

The cutoff is constant before the transition and before the joining
endpoint. Agreement on open overlaps therefore gives the same interior
regularity as the original pieces. Morgan-Tian Proposition 6.30,
pp. 118-119, with the finite-energy endpoint approximation recorded in
proof-work/tasks/M14/derivations/2026-09-21-strict-prefix.md.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)
  (α β : ℝ → G.Point)

/-- The actual patched gauge transition has the regularity of its
pieces throughout the whole open path interval, including both patch
boundaries. Proposition 6.30, pp. 118-119. -/
theorem oneSidedGaugeJoin_contMDiffOn {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    {k : ℕ∞ω} (hk : k ≤ ∞) {A B c r d : ℝ} (hd : 0 < d) (hdr : 2 * d < r)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) k α (Ioo A c))
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) k β (Ioo (c - r) B))
    (hαU : ∀ s ∈ Icc (c - r) c, α s ∈ U)
    (hβU : ∀ s ∈ Icc (c - r) c, β s ∈ U)
    (hαrec : ∀ s ∈ Icc (c - r) c,
      (G.gaugeCover.cylinder b).toSpacetime (lift (α s)) = α s)
    (hβrec : ∀ s ∈ Icc (c - r) c,
      (G.gaugeCover.cylinder b).toSpacetime (lift (β s)) = β s)
    (htime : ∀ s ∈ Icc (c - r) c, (lift (α s)).1 = (lift (β s)).1)
    (hmem : ∀ s ∈ Ioo (c - r) c,
      Proofs.M09.smoothJoinBlend (fun t => (lift (α t)).2.val)
        (fun t => (lift (β t)).2.val) (c - 3 * d / 2) (d / 2) s ∈ G.gaugeCover.spatial b) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) k
      (oneSidedGaugeJoin b lift α β c r d) (Ioo A B) := by
  intro s hs
  by_cases hl : s < c - 2 * d
  · have hsc : s < c := by linarith
    have hreg := (hα s ⟨hs.1, hsc⟩).contMDiffAt (isOpen_Ioo.mem_nhds ⟨hs.1, hsc⟩)
    have heq : oneSidedGaugeJoin b lift α β c r d =ᶠ[𝓝 s] α := by
      filter_upwards [gt_mem_nhds hl] with t ht
      exact oneSidedGaugeJoin_eq_left b lift α β hd hαrec htime ht.le
    exact (hreg.congr_of_eventuallyEq heq).contMDiffWithinAt
  by_cases hr : c - d < s
  · have hcs : c - r < s := by linarith
    have hreg := (hβ s ⟨hcs, hs.2⟩).contMDiffAt (isOpen_Ioo.mem_nhds ⟨hcs, hs.2⟩)
    have heq : oneSidedGaugeJoin b lift α β c r d =ᶠ[𝓝 s] β := by
      filter_upwards [lt_mem_nhds hr] with t ht
      exact oneSidedGaugeJoin_eq_right b lift α β hd hdr hβrec ht.le
    exact (hreg.congr_of_eventuallyEq heq).contMDiffWithinAt
  have hsJ : s ∈ Ioo (c - r) c :=
    ⟨by linarith [not_lt.mp hl], by linarith [not_lt.mp hr]⟩
  have heq : oneSidedGaugeJoin b lift α β c r d =ᶠ[𝓝 s]
      gaugeBlend b lift α β (c - 3 * d / 2) (d / 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hsJ] with t ht
    exact oneSidedGaugeJoin_eq_middle b lift α β ⟨ht.1.le, ht.2⟩
  have hreg := gaugeBlend_contMDiffAt b lift α β hU hlift hk
    ((hα s ⟨hs.1, hsJ.2⟩).contMDiffAt (isOpen_Ioo.mem_nhds ⟨hs.1, hsJ.2⟩))
    ((hβ s ⟨hsJ.1, hs.2⟩).contMDiffAt (isOpen_Ioo.mem_nhds ⟨hsJ.1, hs.2⟩))
    (hαU s (Ioo_subset_Icc_self hsJ)) (hβU s (Ioo_subset_Icc_self hsJ)) (hmem s hsJ)
  exact (hreg.congr_of_eventuallyEq heq).contMDiffWithinAt

end PoincareMT.M14
