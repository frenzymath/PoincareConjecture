import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set

theorem IsPreconnected.subset_or_subset_compl_closure {X : Type*}
    [TopologicalSpace X] {S U : Set X} (hS : IsPreconnected S)
    (hU : IsOpen U) (hdis : Disjoint (frontier U) S) :
    S ⊆ U ∨ S ⊆ (closure U)ᶜ := by
  by_cases hmeet : (S ∩ U).Nonempty
  · exact Or.inl (hS.m76_subset_of_disjoint_frontier hU hdis hmeet)
  · right
    intro x hx hxc
    have hxn : x ∉ U := fun hxU => hmeet ⟨x, hx, hxU⟩
    have hxf : x ∈ frontier U := ⟨hxc, fun hi => hxn (interior_subset hi)⟩
    exact Set.disjoint_left.mp hdis hxf hx

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem IsFinitePLBallPair.isConnected_sdiff {d q : Set X}
    (hd : IsFinitePLBallPair E d q) : IsConnected (d \ q) := by
  obtain ⟨_, C, _, hcv, hne, e, _, heb⟩ := hd
  let I : Set C := (Subtype.val : C → E) ⁻¹' interior C
  have hIimage : (Subtype.val : C → E) '' I = interior C :=
    image_preimage_eq_of_subset (by simpa using (interior_subset : interior C ⊆ C))
  have hIpre : IsPreconnected I := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hIimage]
    exact hcv.interior.isPreconnected
  have hIne : I.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨⟨y, interior_subset hy⟩, hy⟩
  let g : C → X := fun y => e.symm y
  have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hgI : g '' I = d \ q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).property, ?_⟩
      intro hq
      have hf := (heb (e.symm y)).mp hq
      rw [e.apply_symm_apply] at hf
      exact hf.2 hy
    · rintro ⟨hxd, hxq⟩
      let z : d := ⟨x, hxd⟩
      refine ⟨e z, ?_, by simp [g, z]⟩
      by_contra hi
      exact hxq ((heb z).mpr ⟨subset_closure (e z).property, hi⟩)
  rw [← hgI]
  exact (show IsConnected I from ⟨hIne, hIpre⟩).image g hg.continuousOn

theorem closure_inter_eq_frontier_inter_of_disjoint_open {Y : Type*}
    [TopologicalSpace Y] {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (hdis : Disjoint U V) : closure U ∩ closure V = frontier U ∩ frontier V := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨⟨hx.1, ?_⟩, ⟨hx.2, ?_⟩⟩
    · intro hi
      exact Set.disjoint_left.mp (hdis.closure_right hU) (interior_subset hi) hx.2
    · intro hi
      exact Set.disjoint_left.mp (hdis.closure_left hV) hx.1 (interior_subset hi)
  · exact inter_subset_inter frontier_subset_closure frontier_subset_closure

private theorem disjoint_capped_frontier_of_outside
    {Y : Type*} [TopologicalSpace Y] {U V c d q : Set Y}
    (hU : IsOpen U) (hq : q ⊆ d) (hd : d ⊆ frontier U)
    (hVfront : frontier V = c ∪ d) (hc : c \ q ⊆ (closure U)ᶜ) :
    Disjoint (frontier V) U := by
  apply Set.disjoint_left.mpr
  intro x hxf hxU
  have hnotfront : x ∉ frontier U := by
    intro hf
    exact hf.2 (by rwa [hU.interior_eq])
  rw [hVfront] at hxf
  rcases hxf with hxc | hxd
  · by_cases hxq : x ∈ q
    · exact hnotfront (hd (hq hxq))
    · exact hc ⟨hxc, hxq⟩ (subset_closure hxU)
  · exact hnotfront (hd hxd)

theorem alexander_bounded_region_incidence_open [FiniteDimensional ℝ X]
    {b c d q U V : Set X}
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (A : X →ᵃ[ℝ] ℝ) (v : X) (hv : 0 < A.linear v) {a : ℝ}
    (hdplane : d ⊆ {x | A x = a})
    (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hUc : IsConnected U) (hVc : IsConnected V)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d) :
    closure U ∩ closure V = d ∨ U ⊆ V ∨ V ⊆ U := by
  have hqd : q ⊆ d := by rw [← hbd]; exact inter_subset_right
  have hdU : d ⊆ frontier U := by rw [hUf]; exact subset_union_right
  have hdV : d ⊆ frontier V := by rw [hVf]; exact subset_union_right
  have hbU : b ⊆ closure U := by
    exact (show b ⊆ frontier U by rw [hUf]; exact subset_union_left).trans
      frontier_subset_closure
  have hcV : c ⊆ closure V := by
    exact (show c ⊆ frontier V by rw [hVf]; exact subset_union_left).trans
      frontier_subset_closure
  have havoidb : Disjoint (frontier V) (b \ q) := by
    apply Set.disjoint_left.mpr
    intro x hxf hxb
    rw [hVf] at hxf
    rcases hxf with hxc | hxd
    · exact hxb.2 (hbc ▸ And.intro hxb.1 hxc)
    · exact hxb.2 (hbd ▸ And.intro hxb.1 hxd)
  have havoidc : Disjoint (frontier U) (c \ q) := by
    apply Set.disjoint_left.mpr
    intro x hxf hxc
    rw [hUf] at hxf
    rcases hxf with hxb | hxd
    · exact hxc.2 (hbc ▸ And.intro hxb hxc.1)
    · exact hxc.2 (hcd ▸ And.intro hxc.1 hxd)
  have hsideb := hb.isConnected_sdiff.isPreconnected.subset_or_subset_compl_closure
    hV havoidb
  have hsidec := hc.isConnected_sdiff.isPreconnected.subset_or_subset_compl_closure
    hU havoidc
  rcases hsideb with hbin | hbout
  · rcases hsidec with hcin | hcout
    · have hfront : frontier (U ∪ V) ⊆ {x | A x = a} := by
        intro x hxf
        have hxn : x ∉ U ∪ V := by
          intro hx
          exact hxf.2 (by rwa [(hU.union hV).interior_eq])
        have hxcl : x ∈ closure U ∪ closure V := by
          rw [← closure_union]
          exact hxf.1
        apply hdplane
        rcases hxcl with hxU | hxV
        · have hx : x ∈ b ∪ d := hUf ▸
            (show x ∈ frontier U from ⟨hxU, fun hi => hxn (Or.inl (interior_subset hi))⟩)
          rcases hx with hxb | hxd
          · by_cases hxq : x ∈ q
            · exact hqd hxq
            · exact (hxn (Or.inr (hbin ⟨hxb, hxq⟩))).elim
          · exact hxd
        · have hx : x ∈ c ∪ d := hVf ▸
            (show x ∈ frontier V from ⟨hxV, fun hi => hxn (Or.inr (interior_subset hi))⟩)
          rcases hx with hxc | hxd
          · by_cases hxq : x ∈ q
            · exact hqd hxq
            · exact (hxn (Or.inl (hcin ⟨hxc, hxq⟩))).elim
          · exact hxd
      have hempty := (hU.union hV).eq_empty_of_bounded_frontier_subset_affine_level
        (hUb.union hVb) A v hv hfront
      obtain ⟨x, hx⟩ := hUc.nonempty
      exact (Set.notMem_empty x (hempty ▸ Or.inl hx)).elim
    · right
      left
      apply hUc.isPreconnected.m76_subset_of_disjoint_frontier hV
        (disjoint_capped_frontier_of_outside hU hqd hdU hVf hcout)
      obtain ⟨x, hx⟩ := hb.isConnected_sdiff.nonempty
      exact (closure_inter_open_nonempty_iff hV).mp ⟨x, hbU hx.1, hbin hx⟩
  · rcases hsidec with hcin | hcout
    · right
      right
      apply hVc.isPreconnected.m76_subset_of_disjoint_frontier hU
        (disjoint_capped_frontier_of_outside hV hqd hdV hUf hbout)
      obtain ⟨x, hx⟩ := hc.isConnected_sdiff.nonempty
      exact (closure_inter_open_nonempty_iff hU).mp ⟨x, hcV hx.1, hcin hx⟩
    · left
      have havoid := disjoint_capped_frontier_of_outside hU hqd hdU hVf hcout
      have hdis : Disjoint U V := by
        apply Set.disjoint_left.mpr
        intro x hxU hxV
        have hsub := hUc.isPreconnected.m76_subset_of_disjoint_frontier hV havoid
          ⟨x, hxU, hxV⟩
        obtain ⟨y, hy⟩ := hb.isConnected_sdiff.nonempty
        exact hbout hy ((closure_mono hsub) (hbU hy.1))
      rw [closure_inter_eq_frontier_inter_of_disjoint_open hU hV hdis, hUf, hVf]
      apply Subset.antisymm
      · intro x hx
        rcases hx.1 with hxb | hxd
        · rcases hx.2 with hxc | hxd
          · exact hqd (hbc ▸ And.intro hxb hxc)
          · exact hxd
        · exact hxd
      · intro x hx
        exact ⟨Or.inr hx, Or.inr hx⟩

theorem alexander_bounded_region_incidence [FiniteDimensional ℝ X]
    {b c d q U V : Set X}
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (A : X →ᵃ[ℝ] ℝ) (v : X) (hv : 0 < A.linear v) {a : ℝ}
    (hdplane : d ⊆ {x | A x = a})
    (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hUc : IsConnected U) (hVc : IsConnected V)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d) :
    closure U ∩ closure V = d ∨ closure U ⊆ closure V ∨ closure V ⊆ closure U := by
  rcases alexander_bounded_region_incidence_open hb hc hbc hbd hcd A v hv hdplane
    hU hV hUb hVb hUc hVc hUf hVf with hinter | hUV | hVU
  · exact Or.inl hinter
  · exact Or.inr (Or.inl (closure_mono hUV))
  · exact Or.inr (Or.inr (closure_mono hVU))

end Set
