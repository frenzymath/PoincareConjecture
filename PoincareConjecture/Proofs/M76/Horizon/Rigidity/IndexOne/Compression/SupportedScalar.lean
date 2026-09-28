import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.CompactDefiningFunction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.OriginalCompressionScalar
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainIntersection

set_option autoImplicit false
open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

private theorem paste_PL_scalars
    {X α : Type*} [TopologicalSpace X]
    (e : α → OpenPartialHomeomorph X V3) {K U : Set X}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f old : X → ℝ} (hf : Continuous f) (ho : Continuous old)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hoPL : ∀ i, LocallyPiecewiseAffineOn (old ∘ (e i).symm) (e i).target)
    (heq : EqOn f old (U \ K)) :
    ∃ g : X → ℝ, Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g f U ∧ EqOn g old Kᶜ := by
  classical
  let g := U.piecewise f old
  have hgon (x : X) (hx : x ∈ U) : g x = f x := piecewise_eq_of_mem U f old hx
  have hgoff (x : X) (hx : x ∉ K) : g x = old x := by
    by_cases hxU : x ∈ U
    · exact (hgon x hxU).trans (heq ⟨hxU, hx⟩)
    · exact piecewise_eq_of_notMem U f old hxU
  refine ⟨g, ?_, ?_, hgon, hgoff⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · apply hf.continuousAt.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hgon y hy
    · apply ho.continuousAt.congr_of_eventuallyEq
      filter_upwards [hK.isOpen_compl.mem_nhds (show x ∉ K from fun h => hx (hKU h))]
        with y hy
      exact hgoff y hy
  · intro i
    apply LocallyPiecewiseAffineOn.locality
    intro y hy
    by_cases hyU : (e i).symm y ∈ U
    · let T := (e i).target ∩ (e i).symm ⁻¹' U
      have hT : IsOpen T :=
        (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
      have hg : LocallyPiecewiseAffineOn (g ∘ (e i).symm) T :=
        ((hfPL i).mono hT inter_subset_left).congr (fun z hz => (hgon _ hz.2).symm)
      exact ⟨T, ⟨hy, hyU⟩, hg.mono ((e i).open_target.inter hT) inter_subset_right⟩
    · let T := (e i).target ∩ (e i).symm ⁻¹' Kᶜ
      have hT : IsOpen T :=
        (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hK.isOpen_compl
      have hg : LocallyPiecewiseAffineOn (g ∘ (e i).symm) T :=
        ((hoPL i).mono hT inter_subset_left).congr (fun z hz => (hgoff _ hz.2).symm)
      exact ⟨T, ⟨hy, fun h => hyU (hKU h)⟩,
        hg.mono ((e i).open_target.inter hT) inter_subset_right⟩

theorem exists_supported_compression_scalar
    {X α : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {e : α → OpenPartialHomeomorph X V3} {N : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e N j) (hN : IsCompact N) (he : PLDomain e N)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    {U : Set X} (hU : IsOpen U) (hSU : P.closedStrip ⊆ U)
    {old : X → ℝ} (hoc : Continuous old)
    (ho : ∀ i, LocallyPiecewiseAffineOn (old ∘ (e i).symm) (e i).target)
    (hpos : ∀ x, x ∈ interior N ↔ 0 < old x)
    (hzero : ∀ x, x ∈ frontier N ↔ old x = 0)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ x, |old x| ≤ r) :
    ∃ (g : X → ℝ) (A : Set X), IsCompact A ∧ PLDomain e A ∧
      P.closedStrip ⊆ interior A ∧ A ⊆ U ∧ Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g old (interior A)ᶜ ∧ (∀ x, |g x| ≤ r) ∧
      (∀ x, x ∈ interior P.cutCarrier ↔ 0 < g x) ∧
      (∀ x, x ∉ P.cutCarrier ↔ g x < 0) ∧
      g ⁻¹' {0} = (frontier N \ P.openStrip) ∪ P.endDisks := by
  obtain ⟨hcut, hint, hfront, hoverlap, _, _⟩ := P.cut_geometry hN hopen
  have hecut := P.plDomain_cut hN he hopen
  obtain ⟨f, hfc, hf, hsign⟩ := exists_compact_domain_signed_defining_function hecut hcut
  obtain ⟨A, hA, hSA, hAU, hhalfA⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible he.cover
      (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)) hU hSU
  have heA : PLDomain e A := ⟨he.cover, he.compatible, hA.isClosed, hhalfA⟩
  obtain ⟨W, hW, hAW, _, hhalfW⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible he.cover
      hA isOpen_univ (subset_univ A)
  have heW : PLDomain e W := ⟨he.cover, he.compatible, hW.isClosed, hhalfW⟩
  have hdis : Disjoint (frontier W) (frontier (interior A)ᶜ) := by
    rw [heA.frontier_closed_exterior]
    apply disjoint_left.mpr
    intro x hxW hxA
    exact disjoint_left.mp disjoint_interior_frontier (hAW (heA.closed.frontier_subset hxA)) hxW
  have heShell := heW.inter_of_disjoint_frontiers heA.closed_exterior hdis
  have hShell : IsCompact (W ∩ (interior A)ᶜ) := hW.inter_right isOpen_interior.isClosed_compl
  have hUC : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hEC : P.endDisks ⊆ P.closedStrip := hoverlap.symm.subset.trans inter_subset_left
  have hnot (x : X) (hx : x ∉ interior A) : x ∉ P.closedStrip := fun h => hx (hSA h)
  have hiEq (x : X) (hx : x ∉ interior A) :
      x ∈ interior P.cutCarrier ↔ x ∈ interior N := by
    rw [hint]
    exact and_iff_left (hnot x hx)
  have hfEq (x : X) (hx : x ∉ interior A) :
      x ∈ frontier P.cutCarrier ↔ x ∈ frontier N := by
    rw [hfront]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact (hnot x hx (hEC h)).elim
    · exact fun h => Or.inl ⟨h, fun hs => hnot x hx (hUC hs)⟩
  obtain ⟨g0, hg0c, hg0, heq0, hsign0⟩ := heShell.exists_bounded_same_signs_relative
    hShell hfc hoc hf ho
    (fun x hx => (hpos x).symm.trans ((hiEq x hx.2).symm.trans (hsign x).2.2.1))
    (fun x hx => (hzero x).symm.trans ((hfEq x hx.2).symm.trans (hsign x).2.1))
    hr (fun x _ => hbound x)
  obtain ⟨g, hgc, hg, hgon, hgoff⟩ := paste_PL_scalars e hA.isClosed isOpen_interior hAW
    hg0c hoc hg0 ho (fun x hx => heq0 ⟨interior_subset hx.1,
      fun h => hx.2 (interior_subset h)⟩)
  have hfixed : EqOn g old (interior A)ᶜ := by
    intro x hx
    by_cases hxW : x ∈ interior W
    · exact (hgon hxW).trans (heq0 ⟨interior_subset hxW, hx⟩)
    · exact hgoff (fun h => hxW (hAW h))
  have hsg (x : X) : (x ∈ frontier P.cutCarrier ↔ g x = 0) ∧
      (x ∈ interior P.cutCarrier ↔ 0 < g x) ∧ (x ∉ P.cutCarrier ↔ g x < 0) := by
    by_cases hxW : x ∈ interior W
    · rw [hgon hxW]
      exact ⟨(hsign x).2.1.trans (hsign0 x).2.2.1.symm,
        (hsign x).2.2.1.trans (hsign0 x).2.1.symm,
        (hsign x).2.2.2.trans (hsign0 x).2.2.2.symm⟩
    · have hxA : x ∉ interior A := fun h => hxW (hAW (interior_subset h))
      rw [hfixed hxA]
      have hz := (hfEq x hxA).trans (hzero x)
      have hp := (hiEq x hxA).trans (hpos x)
      refine ⟨hz, hp, ?_⟩
      rw [← hecut.closed.closure_eq, closure_eq_interior_union_frontier]
      simp only [mem_union, not_or]
      rw [hp, hz]
      constructor
      · rintro ⟨hp, hz⟩
        exact lt_of_le_of_ne (le_of_not_gt hp) hz
      · intro hn
        exact ⟨not_lt_of_ge hn.le, hn.ne⟩
  refine ⟨g, A, hA, heA, hSA, hAU, hgc, hg, hfixed, ?_,
    fun x => (hsg x).2.1, fun x => (hsg x).2.2, ?_⟩
  · intro x
    by_cases hxW : x ∈ interior W
    · rw [hgon hxW]
      exact (hsign0 x).1
    · rw [hgoff (fun h => hxW (hAW h))]
      exact hbound x
  · ext x
    exact (hsg x).1.symm.trans (Set.ext_iff.mp hfront x)

end PoincareConjecture.M76.HamiltonIntervalTorus
