import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.CriticalSet.Closed
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenSubset
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

open Poincare.Geometry.Manifold.RegularLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

private theorem component_mem_nhds_of_regular
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {c : Real} (q : h ⁻¹' {c})
    (hq : mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0) :
    connectedComponent q ∈ 𝓝 q := by
  let U : Opens S2 := ⟨{x | mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0},
    (Poincare.Geometry.Manifold.isClosed_setOf_mfderiv_eq_zero
      (hh.of_le (by simp))).isOpen_compl⟩
  have hreg : ∀ x ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0 := fun _ hx => hx
  let N := openLevelSet h U c
  let := openLevelSetChartedSpace hh U hreg 1 c
  let := isManifold_openLevelSet hh U hreg 1 c
  let : LocallyConnectedSpace N := ChartedSpace.locallyConnectedSpace
    (EuclideanSpace Real (Fin 1)) N
  let j : N → h ⁻¹' {c} := fun x => ⟨x.1.1, x.2⟩
  have hj : IsEmbedding j := IsEmbedding.subtypeVal.of_comp_iff.mp
    (isEmbedding_openLevelIncl h U c)
  have hrange : range j = Subtype.val ⁻¹' (U : Set S2) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.1.2
    · intro hx
      exact ⟨⟨⟨x.1, hx⟩, x.2⟩, rfl⟩
  have hjo : IsOpenEmbedding j := ⟨hj, by
    rw [hrange]
    exact U.isOpen.preimage continuous_subtype_val⟩
  let z : N := ⟨⟨q, hq⟩, q.property⟩
  have hsub : j '' connectedComponent z ⊆ connectedComponent q :=
    (isPreconnected_connectedComponent.image j hj.continuous.continuousOn).subset_connectedComponent
      ⟨z, mem_connectedComponent, rfl⟩
  exact mem_of_superset (hjo.isOpenMap.image_mem_nhds
    (isOpen_connectedComponent.mem_nhds (mem_connectedComponent (x := z)))) hsub

theorem exists_open_isolating_neighborhood
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2) :
    ∃ O : Set S2, IsOpen O ∧
      connectedComponentIn (h ⁻¹' {h p}) p ⊆ O ∧
      O ∩ h ⁻¹' {h p} = connectedComponentIn (h ⁻¹' {h p}) p := by
  let L := h ⁻¹' {h p}
  let C := connectedComponentIn L p
  have hpL : p ∈ L := rfl
  have hCL : C ⊆ L := connectedComponentIn_subset L p
  obtain ⟨r, hr, hrs⟩ := exists_closedSquare_subset_source e he0
  have hcross : e '' (closedSquare r ∩ {x : E2 | x 0 ^ 2 = x 1 ^ 2}) ⊆ C := by
    simpa only [hep] using square_zeroLevel_subset_component e hr hrs hform
  have hpatch : (e '' openSquare r) ∩ L ⊆ C := by
    rintro q ⟨⟨x, hx, rfl⟩, hq⟩
    have hxs := hrs (openSquare_subset_closedSquare r hx)
    have heq : x 0 ^ 2 = x 1 ^ 2 := by
      change h (e x) = h p at hq
      rw [hform x hxs] at hq
      linarith
    exact hcross ⟨x, ⟨openSquare_subset_closedSquare r hx, heq⟩, rfl⟩
  have hrel : IsOpen ((Subtype.val : L → S2) ⁻¹' C) := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    by_cases hqp : (q : S2) = p
    · have hopen := e.isOpen_image_of_subset_source (isOpen_openSquare r)
        ((openSquare_subset_closedSquare r).trans hrs)
      have hqpatch : (q : S2) ∈ e '' openSquare r :=
        hqp ▸ hep ▸ mem_image_of_mem e (zero_mem_openSquare hr)
      exact mem_of_superset ((hopen.preimage continuous_subtype_val).mem_nhds hqpatch)
        (fun y hy => hpatch ⟨hy, y.property⟩)
    · have hqreg : mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 :=
        fun hc => hqp (hunique q q.property hc)
      apply mem_of_superset (component_mem_nhds_of_regular hh q hqreg)
      intro y hy
      have heq : connectedComponentIn L (q : S2) = C :=
        (connectedComponentIn_eq hq).symm
      change (y : S2) ∈ C
      rw [← heq]
      rw [connectedComponentIn_eq_image q.property]
      exact ⟨y, hy, rfl⟩
  obtain ⟨O, hO, hOC⟩ := isOpen_induced_iff.mp hrel
  have hCO : C ⊆ O := by
    intro q hq
    have : (⟨q, hCL hq⟩ : L) ∈ (Subtype.val : L → S2) ⁻¹' C := hq
    rwa [← hOC] at this
  refine ⟨O, hO, hCO, ?_⟩
  ext q
  constructor
  · rintro ⟨hqO, hqL⟩
    have : (⟨q, hqL⟩ : L) ∈ (Subtype.val : L → S2) ⁻¹' O := hqO
    rwa [hOC] at this
  · intro hq
    exact ⟨hCO hq, hCL hq⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
