import PoincareConjecture.Proofs.M76.Mathlib.HamiltonOverlapCorrection
import PoincareConjecture.Proofs.M76.Mathlib.FiniteChartCover
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover











set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E κ : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]






theorem exists_finite_compatible_family_of_compact_cores
    (hlocal : HasSupportedPLOverlapStraightening (M := M) (E := E))
    (d : κ → OpenPartialHomeomorph M E) (Q : κ → Set M)
    (hQ : ∀ i, IsCompact (Q i)) (hQd : ∀ i, Q i ⊆ (d i).source)
    (t : Finset κ) :
    ∃ s : Finset (OpenPartialHomeomorph M E),
      (∀ i j : s, (i : OpenPartialHomeomorph M E).symm.trans
        (j : OpenPartialHomeomorph M E) ∈ piecewiseAffineGroupoid E) ∧
      (⋃ i ∈ t, Q i) ⊆ ⋃ i : s, (i : OpenPartialHomeomorph M E).source := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨∅, ?_, ?_⟩
    · intro i
      exact (Finset.notMem_empty _ i.property).elim
    · simp
  | @insert j t _ ih =>
    obtain ⟨s, hcompat, hcover⟩ := ih
    let A : Set M := ⋃ i ∈ t, Q i
    have hA : IsCompact A := t.isCompact_biUnion (fun i _ => hQ i)
    have hcore : A ∩ Q j ⊆
        (⋃ i : s, (i : OpenPartialHomeomorph M E).source) ∩ (d j).source :=
      fun _ hx => ⟨hcover hx.1, hQd j hx.2⟩
    obtain ⟨r⟩ := hlocal s hcompat (d j) (A ∩ Q j)
      (hA.inter_right (hQ j).isClosed) hcore
    obtain ⟨_, U, V, C, _, _, _, _, _, _, hU, hV, hAC, hBC, _, _, _,
        _, _, hCC, hsource⟩ :=
      exists_supported_compact_core_chart_insertion
        (fun i : s => (i : OpenPartialHomeomorph M E)) (d j) hcompat
        hA (hQ j) r.neighborhood_open r.support_compact.isClosed
        hcover (hQd j) r.core_subset r.support_subset r.correction r.fixed
        r.coordinates r.coordinates_eq r.locallyPL
    let s' : Finset (OpenPartialHomeomorph M E) := Finset.univ.image C
    have hCmem (i : Option s) : C i ∈ s' :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hnewcover : U ∪ V ⊆ ⋃ i : s', (i : OpenPartialHomeomorph M E).source := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsource.symm.subset hx)
      exact mem_iUnion.mpr ⟨⟨C i, hCmem i⟩, hi⟩
    refine ⟨s', ?_, ?_⟩
    · intro e f
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp e.property
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp f.property
      simpa only [hi, hk] using hCC i k
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨hit, hxi⟩ := mem_iUnion.mp hi
      rcases Finset.mem_insert.mp hit with rfl | hit
      · exact hnewcover (Or.inr (hBC hxi))
      · exact hnewcover (Or.inl (hAC (mem_iUnion.mpr
          ⟨i, mem_iUnion.mpr ⟨hit, hxi⟩⟩)))

end OpenPartialHomeomorph

namespace ChartedSpace

variable {M E : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M]





theorem exists_finite_piecewiseAffine_chart_cover
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening (M := M) (E := E)) :
    ∃ s : Finset (OpenPartialHomeomorph M E),
      (∀ i j : s, (i : OpenPartialHomeomorph M E).symm.trans
        (j : OpenPartialHomeomorph M E) ∈ piecewiseAffineGroupoid E) ∧
      ∀ x : M, ∃ i : s, x ∈ (i : OpenPartialHomeomorph M E).source := by
  obtain ⟨t, V, _, _, hVs, hVc, hfull⟩ := exists_finite_shrunk_chart_cover E (M := M)
  obtain ⟨s, hcompat, hcover⟩ :=
    OpenPartialHomeomorph.exists_finite_compatible_family_of_compact_cores
      hlocal (chartAt E) (fun x => closure (V x)) hVc hVs t
  refine ⟨s, hcompat, ?_⟩
  intro x
  have hx : x ∈ ⋃ y ∈ t, V y := hfull.symm ▸ mem_univ x
  obtain ⟨y, hy⟩ := mem_iUnion.mp hx
  obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mp (hcover (mem_iUnion.mpr
    ⟨y, mem_iUnion.mpr ⟨hyt, subset_closure hxy⟩⟩))





theorem exists_piecewiseAffine_chartedSpace
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening (M := M) (E := E)) :
    ∃ a : ChartedSpace E M, letI := a; HasGroupoid M (piecewiseAffineGroupoid E) := by
  obtain ⟨s, hcompat, hcover⟩ := exists_finite_piecewiseAffine_chart_cover hlocal
  exact ⟨ofChartCover (fun i : s => (i : OpenPartialHomeomorph M E)) hcover,
    hasGroupoid_ofChartCover (fun i : s => (i : OpenPartialHomeomorph M E)) hcover
      (piecewiseAffineGroupoid E) hcompat⟩

end ChartedSpace
