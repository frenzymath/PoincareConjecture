import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryBumping
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.CriticalSet.Closed
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenSubset
import Mathlib.SetTheory.Cardinal.Finite








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private theorem frontier_patch_subset {M : Type*} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph E2 M) {r : Real} (hr : 0 < r)
    (hrs : closedSquare r ⊆ e.source) :
    frontier (e '' openSquare r) ⊆ e '' (closedSquare r \ openSquare r) := by
  have hcompact : IsCompact (e '' closedSquare r) :=
    (isCompact_closedSquare hr.le).image_of_continuousOn (e.continuousOn.mono hrs)
  have hclosed : closure (e '' openSquare r) ⊆ e '' closedSquare r :=
    closure_minimal (image_mono (openSquare_subset_closedSquare r)) hcompact.isClosed
  have hopen := e.isOpen_image_of_subset_source (isOpen_openSquare r)
    ((openSquare_subset_closedSquare r).trans hrs)
  intro q hq
  have hqc := hclosed (frontier_subset_closure hq)
  obtain ⟨x, hx, rfl⟩ := hqc
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  intro hxo
  exact (hopen.frontier_eq ▸ hq).2 (mem_image_of_mem e hxo)



theorem compact_regular_exterior
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (_he0 : 0 ∈ e.source) (hep : e 0 = p)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
      let C := connectedComponentIn (h ⁻¹' {h p}) p
      let K := C \ e '' openSquare r
      Function.Injective (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
      K ∩ e '' closedSquare r = range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
      IsCompact K ∧
      (∀ q ∈ K, mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0) ∧
      (∀ q ∈ K, ∃ i : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn K q) ∧
      Finite (ConnectedComponents K) := by
  classical
  let C := connectedComponentIn (h ⁻¹' {h p}) p
  let V := e '' openSquare r
  let K := C \ V
  have hopen : IsOpen V := e.isOpen_image_of_subset_source (isOpen_openSquare r)
    ((openSquare_subset_closedSquare r).trans hrs)
  have hpL : p ∈ h ⁻¹' {h p} := rfl
  have hpC : p ∈ C := mem_connectedComponentIn hpL
  have hpV : p ∈ V := hep ▸ mem_image_of_mem e (zero_mem_openSquare hr)
  have hC : IsCompact C := by
    let L := h ⁻¹' {h p}
    let : CompactSpace L :=
      isCompact_iff_compactSpace.mp (isClosed_singleton.preimage hh.continuous).isCompact
    rw [show C = connectedComponentIn L p from rfl, connectedComponentIn_eq_image hpL]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hpL
  have hcross : e '' (closedSquare r ∩ {x : E2 | x 0 ^ 2 = x 1 ^ 2}) ⊆ C := by
    simpa only [hep] using square_zeroLevel_subset_component e hr hrs hform
  have hcontacts (i : Fin 2 × Fin 2) : e (contact r i) ∈ K ∩ e '' closedSquare r := by
    have hi := contact_mem hr i
    have his := hrs hi.1.1
    refine ⟨⟨hcross ⟨_, ⟨hi.1.1, hi.2⟩, rfl⟩, ?_⟩,
      mem_image_of_mem e hi.1.1⟩
    rintro ⟨x, hx, heq⟩
    have hxs := hrs (openSquare_subset_closedSquare r hx)
    have hxi := e.injOn hxs his heq
    exact hi.1.2 (hxi ▸ hx)
  have hboundary : K ∩ e '' closedSquare r =
      range (fun i : Fin 2 × Fin 2 => e (contact r i)) := by
    ext q
    constructor
    · rintro ⟨hqK, x, hx, rfl⟩
      have hqx : x 0 ^ 2 = x 1 ^ 2 := by
        have hlev := connectedComponentIn_subset (h ⁻¹' {h p}) p hqK.1
        change h (e x) = h p at hlev
        rw [hform x (hrs hx)] at hlev
        linarith
      have hxo : x ∉ openSquare r := fun hxopen => hqK.2 ⟨x, hxopen, rfl⟩
      have hxi : x ∈ range (contact r) :=
        square_boundary_zeroLevel hr ▸ (show x ∈
          (closedSquare r \ openSquare r) ∩ {x : E2 | x 0 ^ 2 = x 1 ^ 2}
          from ⟨⟨hx, hxo⟩, hqx⟩)
      obtain ⟨i, rfl⟩ := hxi
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact hcontacts i
  have hattach : ∀ q ∈ K, ∃ i : Fin 2 × Fin 2,
      e (contact r i) ∈ connectedComponentIn K q := by
    intro q hq
    obtain ⟨y, hy, hyfront⟩ :=
      Poincare.Topology.connectedComponentIn_diff_inter_frontier_nonempty
        hC hconn hopen ⟨p, hpC, hpV⟩ hq
    have hyK := connectedComponentIn_subset K q hy
    obtain ⟨x, hx, heq⟩ := frontier_patch_subset e hr hrs hyfront
    have hybound : y ∈ K ∩ e '' closedSquare r := ⟨hyK, x, hx.1, heq⟩
    rw [hboundary] at hybound
    obtain ⟨i, rfl⟩ := hybound
    exact ⟨i, hy⟩
  have hfinite : Finite (ConnectedComponents K) := by
    let j : Fin 2 × Fin 2 → K := fun i => ⟨e (contact r i), (hcontacts i).1⟩
    apply Finite.of_surjective (fun i => ConnectedComponents.mk (j i))
    intro Z
    obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe Z
    obtain ⟨i, hi⟩ := hattach q q.property
    refine ⟨i, ConnectedComponents.coe_eq_coe'.mpr ?_⟩
    rw [connectedComponentIn_eq_image q.property] at hi
    obtain ⟨y, hy, heq⟩ := hi
    have hyj : y = j i := Subtype.ext heq
    exact hyj ▸ hy
  refine ⟨?_, hboundary, hC.diff hopen, ?_, hattach, hfinite⟩
  · intro i j hij
    exact contact_injective hr (e.injOn (hrs (contact_mem hr i).1.1)
      (hrs (contact_mem hr j).1.1) hij)
  · intro q hq hc
    have hlev := connectedComponentIn_subset (h ⁻¹' {h p}) p hq.1
    have hqp := hunique q hlev hc
    exact hq.2 (hqp ▸ hpV)



theorem exists_compact_regular_exterior
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2) :
    ∃ r : Real, 0 < r ∧ closedSquare r ⊆ e.source ∧
      let C := connectedComponentIn (h ⁻¹' {h p}) p
      let K := C \ e '' openSquare r
      Function.Injective (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
      K ∩ e '' closedSquare r = range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
      IsCompact K ∧
      (∀ q ∈ K, mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0) ∧
      (∀ q ∈ K, ∃ i : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn K q) ∧
      Finite (ConnectedComponents K) := by
  obtain ⟨r, hr, hrs⟩ := exists_closedSquare_subset_source e he0
  exact ⟨r, hr, hrs, compact_regular_exterior hh hunique e he0 hep hform hr hrs⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
