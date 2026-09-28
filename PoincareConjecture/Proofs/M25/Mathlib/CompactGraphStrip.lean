import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Topology

namespace OpenPartialHomeomorph

theorem compact_graph_strip
    {K E : Type*} [TopologicalSpace K] [CompactSpace K] [ConnectedSpace K]
    [TopologicalSpace E] [T2Space E]
    (e : OpenPartialHomeomorph (K × ℝ) E)
    (f g : K → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hlt : ∀ q, f q < g q) {c d : ℝ}
    (hbound : ∀ q, c ≤ f q ∧ g q ≤ d)
    (hsource : {z : K × ℝ | f z.1 ≤ z.2 ∧ z.2 ≤ g z.1} ⊆ e.source) :
    let D : Set E := e '' {z : K × ℝ | f z.1 < z.2 ∧ z.2 < g z.1}
    IsOpen D ∧ IsConnected D ∧
      closure D = e '' {z : K × ℝ | f z.1 ≤ z.2 ∧ z.2 ≤ g z.1} ∧
      IsCompact (closure D) ∧
      frontier D = (Set.range fun q => e (q, f q)) ∪
        (Set.range fun q => e (q, g q)) := by
  let O : Set (K × ℝ) := {z | f z.1 < z.2 ∧ z.2 < g z.1}
  let B : Set (K × ℝ) := {z | f z.1 ≤ z.2 ∧ z.2 ≤ g z.1}
  let D : Set E := e '' O
  change IsOpen D ∧ IsConnected D ∧ closure D = e '' B ∧ _
  have hOB : O ⊆ B := fun _ hz => ⟨hz.1.le, hz.2.le⟩
  have hOsource : O ⊆ e.source := hOB.trans hsource
  have hOopen : IsOpen O :=
    (isOpen_lt (hf.comp continuous_fst) continuous_snd).inter
      (isOpen_lt continuous_snd (hg.comp continuous_fst))
  have hDopen : IsOpen D := e.isOpen_image_of_subset_source hOopen hOsource
  have hDconn : IsConnected D :=
    (isConnected_between_continuous_graphs hf hg hlt).image e (e.continuousOn.mono hOsource)
  have hBclosed : IsClosed B :=
    (isClosed_le (hf.comp continuous_fst) continuous_snd).inter
      (isClosed_le continuous_snd (hg.comp continuous_fst))
  have hBcompact : IsCompact B :=
    (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc c d))).of_isClosed_subset hBclosed
      (fun z hz => ⟨mem_univ _, (hbound z.1).1.trans hz.1, hz.2.trans (hbound z.1).2⟩)
  have hEBcompact : IsCompact (e '' B) :=
    hBcompact.image_of_continuousOn (e.continuousOn.mono hsource)
  have hclosure : closure D = e '' B := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono hOB) hEBcompact.isClosed
    · rintro x ⟨⟨q, s⟩, hz, rfl⟩
      have hc : ContinuousAt (fun t : ℝ => e (q, t)) s :=
        (e.continuousOn.continuousAt (e.open_source.mem_nhds (hsource hz))).comp
          (continuous_const.prodMk continuous_id).continuousAt
      apply hc.continuousWithinAt.mem_closure (s := Ioo (f q) (g q))
      · rw [closure_Ioo (hlt q).ne]
        exact hz
      · intro t ht
        exact ⟨(q, t), ht, rfl⟩
  refine ⟨hDopen, hDconn, hclosure, hclosure.symm ▸ hEBcompact, ?_⟩
  rw [frontier, hDopen.interior_eq, hclosure]
  apply Subset.antisymm
  · rintro x ⟨⟨⟨q, s⟩, hz, rfl⟩, hn⟩
    rcases eq_or_lt_of_le hz.1 with he | hl
    · exact Or.inl ⟨q, congrArg (fun t => e (q, t)) he⟩
    · rcases eq_or_lt_of_le hz.2 with he | hr
      · exact Or.inr ⟨q, congrArg (fun t => e (q, t)) he.symm⟩
      · exact False.elim (hn ⟨(q, s), ⟨hl, hr⟩, rfl⟩)
  · rintro x (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · have hz : (q, f q) ∈ B := ⟨le_rfl, (hlt q).le⟩
      refine ⟨⟨(q, f q), hz, rfl⟩, ?_⟩
      rintro ⟨z, hzo, he⟩
      have hez : z = (q, f q) := e.injOn (hOsource hzo) (hsource hz) he
      rw [hez] at hzo
      exact (lt_irrefl (f q)) hzo.1
    · have hz : (q, g q) ∈ B := ⟨(hlt q).le, le_rfl⟩
      refine ⟨⟨(q, g q), hz, rfl⟩, ?_⟩
      rintro ⟨z, hzo, he⟩
      have hez : z = (q, g q) := e.injOn (hOsource hzo) (hsource hz) he
      rw [hez] at hzo
      exact (lt_irrefl (g q)) hzo.2

end OpenPartialHomeomorph
