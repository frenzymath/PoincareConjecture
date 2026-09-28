import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset

noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Topology
namespace Poincare.Topology.Manifold

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (n + 2))

private theorem isPreconnected_of_dense_local {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {S : Set X} (hS : Dense S)
    (hlocal : ∀ p : X, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ IsPreconnected (U ∩ S)) :
    IsPreconnected S := by
  apply isPreconnected_closed_iff.mpr
  intro A B hA hB hcover hneA hneB
  by_contra hnone
  have hsep : ∀ x ∈ S, x ∈ A → x ∈ B → False :=
    fun x hx ha hb => hnone ⟨x, hx, ha, hb⟩
  have hlocal_side (p : X) : p ∈ interior A ∪ interior B := by
    obtain ⟨U, hU, hpU, hconn⟩ := hlocal p
    have hside : U ∩ S ⊆ A ∨ U ∩ S ⊆ B := by
      by_cases hmeet : (U ∩ S ∩ A).Nonempty
      · left
        intro x hx
        rcases hcover hx.2 with ha | hb
        · exact ha
        · obtain ⟨y, hy, hya, hyb⟩ := isPreconnected_closed_iff.mp hconn A B hA hB
            (fun z hz => hcover hz.2) hmeet ⟨x, hx, hb⟩
          exact (hsep y hy.2 hya hyb).elim
      · right
        intro x hx
        exact (hcover hx.2).resolve_left (fun ha => hmeet ⟨x, hx, ha⟩)
    have hclosure : U ⊆ closure (U ∩ S) := by
      intro x hx
      apply _root_.mem_closure_iff.mpr
      intro W hW hxW
      obtain ⟨y, ⟨hyW, hyU⟩, hyS⟩ :=
        hS.inter_open_nonempty (W ∩ U) (hW.inter hU) ⟨x, hxW, hx⟩
      exact ⟨y, hyW, hyU, hyS⟩
    rcases hside with ha | hb
    · exact Or.inl (interior_maximal (hclosure.trans (closure_minimal ha hA)) hU hpU)
    · exact Or.inr (interior_maximal (hclosure.trans (closure_minimal hb hB)) hU hpU)
  have hinter : (interior A ∩ interior B).Nonempty := by
    apply nonempty_inter isOpen_interior isOpen_interior
    · exact eq_univ_of_forall hlocal_side
    · obtain ⟨x, hxS, hxA⟩ := hneA
      exact ⟨x, (hlocal_side x).resolve_right (fun hxB => hsep x hxS hxA (interior_subset hxB))⟩
    · obtain ⟨x, hxS, hxB⟩ := hneB
      exact ⟨x, (hlocal_side x).resolve_left (fun hxA => hsep x hxS (interior_subset hxA) hxB)⟩
  obtain ⟨x, ⟨hxA, hxB⟩, hxS⟩ :=
    hS.inter_open_nonempty _ (isOpen_interior.inter isOpen_interior) hinter
  exact hsep x hxS (interior_subset hxA) (interior_subset hxB)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [hM : ChartedSpace (E n) M]

include hM

theorem dense_compl_countable {C : Set M} (hC : C.Countable) : Dense Cᶜ := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p, hp⟩
  let c := chartAt (E n) p
  have hpc : p ∈ c.source := mem_chart_source _ p
  have hO : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.symm.isOpen_inter_preimage hU
  have hpO : c p ∈ c.target ∩ c.symm ⁻¹' U := by
    exact ⟨c.map_source hpc, by simpa only [mem_preimage, c.left_inv hpc] using hp⟩
  obtain ⟨z, hzO, hzC⟩ := ((hC.image c).dense_compl (𝕜 := ℝ)).inter_open_nonempty
    _ hO ⟨c p, hpO⟩
  refine ⟨c.symm z, hzO.2, ?_⟩
  intro hz
  exact hzC ⟨c.symm z, hz, c.right_inv hzO.1⟩

theorem isPathConnected_chart_ball_sdiff_countable (p : M) {r : ℝ} (hr : 0 < r)
    (htarget : ball (chartAt (E n) p p) r ⊆ (chartAt (E n) p).target)
    {C : Set M} (hC : C.Countable) :
    IsPathConnected (((chartAt (E n) p).symm '' ball (chartAt (E n) p p) r) \ C) := by
  let c := chartAt (E n) p
  let B : OpenPartialHomeomorph (E n) (E n) := OpenPartialHomeomorph.univBall (c p) r
  have hBsource : B.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hBtarget : B.target = ball (c p) r := OpenPartialHomeomorph.univBall_target _ hr
  have hBmem (z : E n) : B z ∈ ball (c p) r := by
    rw [← hBtarget]
    exact B.map_source (hBsource ▸ mem_univ z)
  let g : E n → M := c.symm ∘ B
  have hg : Continuous g := c.continuousOn_symm.comp_continuous
    (OpenPartialHomeomorph.continuous_univBall _ _) (fun z => htarget (hBmem z))
  have hginj : Function.Injective g := by
    intro z w h
    apply B.injOn (hBsource ▸ mem_univ z) (hBsource ▸ mem_univ w)
    exact c.symm.injOn (htarget (hBmem z)) (htarget (hBmem w)) h
  have hpre : (g ⁻¹' C).Countable := hC.preimage hginj
  have hrank : 1 < Module.rank ℝ (E n) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < n + 2 by omega)
  have hconn := (hpre.isPathConnected_compl_of_one_lt_rank hrank).image hg
  have himage : g '' (g ⁻¹' C)ᶜ = (c.symm '' ball (c p) r) \ C := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨B z, hBmem z, rfl⟩, hz⟩
    · rintro ⟨⟨z, hz, rfl⟩, hnot⟩
      obtain ⟨w, _, hw⟩ := B.surjOn (hBtarget.symm ▸ hz)
      refine ⟨w, ?_, ?_⟩
      · change c.symm (B w) ∉ C
        simpa only [hw] using hnot
      · simp only [g, Function.comp_apply, hw]
  rwa [himage] at hconn

theorem isPreconnected_compl_countable [PreconnectedSpace M]
    {C : Set M} (hC : C.Countable) : IsPreconnected Cᶜ := by
  apply isPreconnected_of_dense_local (dense_compl_countable (n := n) hC)
  intro p
  let c := chartAt (E n) p
  obtain ⟨r, hr, htarget⟩ := Metric.mem_nhds_iff.mp
    (c.open_target.mem_nhds (c.map_source (mem_chart_source _ p)))
  refine ⟨c.symm '' ball (c p) r, c.isOpen_image_symm_of_subset_target isOpen_ball htarget,
    ⟨c p, mem_ball_self hr, c.left_inv (mem_chart_source _ p)⟩, ?_⟩
  exact (isPathConnected_chart_ball_sdiff_countable p hr htarget hC).isConnected.isPreconnected

theorem isConnected_compl_countable [ConnectedSpace M]
    {C : Set M} (hC : C.Countable) : IsConnected Cᶜ :=
  ⟨(dense_compl_countable (n := n) hC).nonempty, isPreconnected_compl_countable (n := n) hC⟩

theorem locallyPathConnectedSpace_compl_countable
    {C : Set M} (hC : C.Countable) : LocallyPathConnectedSpace ↥(Cᶜ) := by
  constructor
  intro x
  rw [hasBasis_self]
  intro t ht
  obtain ⟨U, hUx, hUt⟩ := (mem_nhds_subtype Cᶜ x t).mp ht
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  let c := chartAt (E n) (x : M)
  have hxs : (x : M) ∈ c.source := mem_chart_source _ _
  have hO : IsOpen (c.target ∩ c.symm ⁻¹' V) := c.symm.isOpen_inter_preimage hV
  have hxc : c (x : M) ∈ c.target ∩ c.symm ⁻¹' V :=
    ⟨c.map_source hxs, by simpa only [mem_preimage, c.left_inv hxs] using hxV⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hxc)
  have htarget : ball (c x) r ⊆ c.target := hball.trans inter_subset_left
  let B := c.symm '' ball (c x) r
  have hB : IsOpen B := c.isOpen_image_symm_of_subset_target isOpen_ball htarget
  have hxB : (x : M) ∈ B := ⟨c x, mem_ball_self hr, c.left_inv hxs⟩
  have hBV : B ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    exact (hball hz).2
  refine ⟨(Subtype.val : ↥(Cᶜ) → M) ⁻¹' B,
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hB.mem_nhds hxB), ?_, ?_⟩
  · apply _root_.Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
    have he : (Subtype.val : ↥(Cᶜ) → M) '' ((Subtype.val : ↥(Cᶜ) → M) ⁻¹' B) = B \ C := by
      ext y
      simp [and_comm]
    rw [he]
    exact isPathConnected_chart_ball_sdiff_countable (x : M) hr htarget hC
  · intro y hy
    exact hUt (hVU (hBV hy))

theorem isPathConnected_compl_countable [ConnectedSpace M]
    {C : Set M} (hC : C.Countable) : IsPathConnected Cᶜ := by
  let : ConnectedSpace ↥(Cᶜ) := isConnected_iff_connectedSpace.mp (isConnected_compl_countable (n := n) hC)
  let : LocallyPathConnectedSpace ↥(Cᶜ) := locallyPathConnectedSpace_compl_countable (n := n) hC
  exact isPathConnected_iff_pathConnectedSpace.mpr
    PathConnectedSpace.of_locallyPathConnectedSpace

theorem isPreconnected_sdiff_countable_of_isOpen
    {U C : Set M} (hU : IsOpen U) (hconn : IsPreconnected U) (hC : C.Countable) :
    IsPreconnected (U \ C) := by
  let O : TopologicalSpace.Opens M := ⟨U, hU⟩
  let : PreconnectedSpace O := isPreconnected_iff_preconnectedSpace.mp hconn
  have hc : ((Subtype.val : O → M) ⁻¹' C).Countable := hC.preimage Subtype.val_injective
  have hp := (isPreconnected_compl_countable (n := n) hc).image
    Subtype.val continuous_subtype_val.continuousOn
  have he : (Subtype.val : O → M) '' ((Subtype.val : O → M) ⁻¹' C)ᶜ = U \ C := by
    ext x
    simp [O, and_comm]
  rwa [he] at hp

theorem isConnected_sdiff_countable_of_isOpen
    {U C : Set M} (hU : IsOpen U) (hconn : IsConnected U) (hC : C.Countable) :
    IsConnected (U \ C) := by
  refine ⟨?_, isPreconnected_sdiff_countable_of_isOpen (n := n) hU hconn.isPreconnected hC⟩
  obtain ⟨x, hxU, hxC⟩ :=
    (dense_compl_countable (n := n) hC).inter_open_nonempty U hU hconn.nonempty
  exact ⟨x, hxU, hxC⟩

theorem isPathConnected_sdiff_countable_of_isOpen
    {U C : Set M} (hU : IsOpen U) (hconn : IsConnected U) (hC : C.Countable) :
    IsPathConnected (U \ C) := by
  let O : TopologicalSpace.Opens M := ⟨U, hU⟩
  let : ConnectedSpace O := isConnected_iff_connectedSpace.mp hconn
  have hc : ((Subtype.val : O → M) ⁻¹' C).Countable := hC.preimage Subtype.val_injective
  have hp := (isPathConnected_compl_countable (n := n) hc).image continuous_subtype_val
  have he : (Subtype.val : O → M) '' ((Subtype.val : O → M) ⁻¹' C)ᶜ = U \ C := by
    ext x
    simp [O, and_comm]
  rwa [he] at hp

omit hM in

theorem isDiscrete_of_eventually_eq {C : Set M}
    (hiso : ∀ x ∈ C, ∀ᶠ y in 𝓝 x, y ∈ C → y = x) : IsDiscrete C := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (hiso x hx)
  refine ⟨U, hU, ?_⟩
  ext y
  constructor
  · rintro ⟨hyU, hyC⟩
    exact hUsub hyU hyC
  · rintro rfl
    exact ⟨hxU, hx⟩

theorem isPathConnected_sdiff_of_isOpen_of_isolated
    [SecondCountableTopology M] {U C : Set M}
    (hU : IsOpen U) (hconn : IsConnected U)
    (hiso : ∀ x ∈ C, ∀ᶠ y in 𝓝 x, y ∈ C → y = x) :
    IsPathConnected (U \ C) := by
  exact isPathConnected_sdiff_countable_of_isOpen (n := n) hU hconn
    ((HereditarilyLindelofSpace.isLindelof C).countable_of_isDiscrete
      (isDiscrete_of_eventually_eq hiso))

theorem isPathConnected_sdiff_compact_of_isOpen_of_isolated
    {U C : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    (hcompact : IsCompact C)
    (hiso : ∀ x ∈ C, ∀ᶠ y in 𝓝 x, y ∈ C → y = x) :
    IsPathConnected (U \ C) := by
  exact isPathConnected_sdiff_countable_of_isOpen (n := n) hU hconn
    (hcompact.finite (isDiscrete_of_eventually_eq hiso)).countable

end Poincare.Topology.Manifold
