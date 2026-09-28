import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLGraphBlock
import PoincareConjecture.Proofs.M76.Mathlib.PLBandCutoff
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Topology.Compactness.LocallyCompact













set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_compactly_supported_PL_core_cutoff
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {A W : Set M} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ (w : M → ℝ) (C V : Set M),
      IsCompact C ∧ C ⊆ W ∧ IsOpen V ∧ A ⊆ V ∧ Continuous w ∧
      (∀ x, w x ∈ Icc 0 1) ∧ EqOn w (fun _ => 1) V ∧
      (∀ x, x ∉ C → w x = 0) ∧
      ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target := by
  classical
  have hchoose (x : A) : ∃ (i : ι) (Q : Set M),
      IsCompact Q ∧ (x : M) ∈ interior Q ∧ Q ⊆ (e i).source ∩ W := by
    obtain ⟨i, hxi⟩ := hcover x
    obtain ⟨Q, hQ, hxQ, hQi⟩ := exists_compact_subset
      ((e i).open_source.inter hW) ⟨hxi, hAW x.property⟩
    exact ⟨i, Q, hQ, hxQ, hQi⟩
  choose i Q hQ hxQ hQi using hchoose
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover (fun x : A => interior (Q x))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxQ ⟨x, hx⟩⟩)
  have hblock (a : A) : ∃ (w : M → ℝ) (C : Set M),
      IsCompact C ∧ C ⊆ W ∧ Continuous w ∧ (∀ x, w x ∈ Icc 0 1) ∧
      EqOn w (fun _ => 1) (Q a) ∧ (∀ x, x ∉ C → w x = 0) ∧
      ∀ j, LocallyPiecewiseAffineOn (w ∘ (e j).symm) (e j).target := by
    let d := (e (i a)).restr W
    have hQd : Q a ⊆ d.source := by
      simpa only [d, restr_source' _ _ hW] using hQi a
    obtain ⟨f, C, hC, hCd, hfc, hfzero, hfone, hfunit, _, hfPL⟩ :=
      d.exists_compactly_supported_PL_graph_block (hQ a) hQd
    refine ⟨fun x => (f x).1, C, hC, ?_, hfc.fst, hfunit,
      fun x hx => congrArg Prod.fst (hfone hx), ?_, ?_⟩
    · intro x hx
      have hxd := hCd hx
      rw [show d.source = (e (i a)).source ∩ W from restr_source' _ _ hW] at hxd
      exact hxd.2
    · intro x hx
      simp [hfzero x hx]
    · intro j
      have hjd : (e j).symm.trans d ∈ piecewiseAffineGroupoid E := by
        apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
        have hji := ((mem_piecewiseAffineGroupoid_iff E _).mp (hcompat j (i a))).1
        apply hji.mono ((e j).symm.trans d).open_source
        intro x hx
        refine ⟨hx.1, ?_⟩
        have hx' : (e j).symm x ∈ d.source := hx.2
        rw [show d.source = (e (i a)).source ∩ W from restr_source' _ _ hW] at hx'
        exact hx'.1
      have hfst := locallyPiecewiseAffineOn_affine
        (ContinuousLinearMap.fst ℝ ℝ E).toContinuousAffineMap isOpen_univ
      have hcomp := hfst.comp (hfPL (e j) hjd)
      rw [preimage_univ, inter_univ] at hcomp
      exact hcomp.congr (fun _ _ => rfl)
  choose g C hC hCW hgc hgu hgone hgzero hgPL using hblock
  have hfinite (t : Finset A) : ∃ (w : M → ℝ) (D : Set M),
      IsCompact D ∧ D ⊆ W ∧ Continuous w ∧ (∀ x, w x ∈ Icc 0 1) ∧
      (∀ a ∈ t, EqOn w (fun _ => 1) (Q a)) ∧
      (∀ x, x ∉ D → w x = 0) ∧
      ∀ j, LocallyPiecewiseAffineOn (w ∘ (e j).symm) (e j).target := by
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, ∅, isCompact_empty, empty_subset _, continuous_const,
        fun _ => ⟨le_rfl, by norm_num⟩, ?_, fun _ _ => rfl, ?_⟩
      · simp
      · intro j
        exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ E 0)
          (e j).open_target
    | @insert a t _ ih =>
      obtain ⟨w, D, hD, hDW, hwc, hwu, hwone, hwzero, hwPL⟩ := ih
      refine ⟨fun x => max (g a x) (w x), C a ∪ D, (hC a).union hD,
        union_subset (hCW a) hDW, (hgc a).max hwc, ?_, ?_, ?_, ?_⟩
      · intro x
        exact ⟨(hgu a x).1.trans (le_max_left _ _), max_le (hgu a x).2 (hwu x).2⟩
      · intro b hb x hx
        change max (g a x) (w x) = 1
        rcases Finset.mem_insert.mp hb with hba | hbt
        · subst b
          rw [hgone a hx]
          exact max_eq_left (hwu x).2
        · rw [hwone b hbt hx]
          exact max_eq_right (hgu a x).2
      · intro x hx
        change max (g a x) (w x) = 0
        rw [hgzero a x (fun h => hx (Or.inl h)), hwzero x (fun h => hx (Or.inr h)),
          max_self]
      · intro j
        exact (hgPL a j).max (hwPL j)
  obtain ⟨w, D, hD, hDW, hwc, hwu, hwone, hwzero, hwPL⟩ := hfinite s
  refine ⟨w, D, ⋃ a ∈ s, interior (Q a), hD, hDW,
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_interior,
    hs, hwc, hwu, ?_, hwzero, hwPL⟩
  intro x hx
  obtain ⟨a, has, hxQ⟩ := mem_iUnion₂.mp hx
  exact hwone a has (interior_subset hxQ)

omit [LocallyCompactSpace M] in




theorem isCompact_core_cutoff_superlevel
    {w : M → ℝ} {A C W : Set M} (hw : Continuous w)
    (hC : IsCompact C) (hCW : C ⊆ W)
    (hzero : ∀ x, x ∉ C → w x = 0) (hone : EqOn w (fun _ => 1) A)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsCompact {x | t ≤ w x} ∧ A ⊆ interior {x | t ≤ w x} ∧
      {x | t ≤ w x} ⊆ W := by
  have hKC : {x | t ≤ w x} ⊆ C := by
    intro x hx
    by_contra hxc
    have hx' : t ≤ w x := hx
    rw [hzero x hxc] at hx'
    exact (not_le_of_gt ht0) hx'
  refine ⟨hC.of_isClosed_subset (isClosed_le continuous_const hw) hKC, ?_, hKC.trans hCW⟩
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset ((isOpen_lt continuous_const hw).mem_nhds ?_)
    (show {y | t < w y} ⊆ {y | t ≤ w y} from
      fun y hy => (show t < w y from hy).le)
  change t < w x
  rw [hone hx]
  exact ht1

end OpenPartialHomeomorph
