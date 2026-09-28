import PoincareConjecture.Proofs.M02.SimplicialCW











set_option autoImplicit false

open Set Metric Topology

universe u

namespace PoincareConjecture.Proofs.M02



theorem exists_simplex_face_intrinsicInterior
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (s : Finset F) (hne : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → F)) {x : F}
    (hx : x ∈ convexHull ℝ (s : Set F)) :
    ∃ t : Finset F, t ⊆ s ∧ t.Nonempty ∧
      x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set F)) := by
  classical
  induction hne using Finset.Nonempty.strong_induction with
  | @h₀ a =>
      exact ⟨{a}, Finset.singleton_subset_iff.mpr (by simp),
        Finset.singleton_nonempty _, by
          simpa [convexHull_singleton, intrinsicInterior_singleton] using hx⟩
  | @h₁ s hs ih =>
      by_cases hxi : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set F))
      · exact ⟨s, Finset.Subset.rfl, hs.nonempty, hxi⟩
      · have hfront : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set F)) := by
          rw [← closure_sdiff_intrinsicInterior]
          exact ⟨subset_closure hx, hxi⟩
        rw [simplex_intrinsicFrontier s hs.nonempty hi] at hfront
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hfront
        have hne' : (s.erase (i : F)).Nonempty := by
          exact Finset.coe_nonempty.mp
            (convexHull_nonempty_iff.mp ⟨x, hxi⟩)
        have hi' : AffineIndependent ℝ ((↑) : (s.erase (i : F)) → F) :=
          hi.mono (Finset.erase_subset _ _)
        obtain ⟨t, ht, htne, htx⟩ := ih (s.erase (i : F)) hne'
          (Finset.erase_ssubset i.property) hi' hxi
        exact ⟨t, ht.trans (Finset.erase_subset _ _), htne, htx⟩



noncomputable abbrev exists_cwComplex_of_finite_section
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (S : Set F) (K : Geometry.SimplicialComplex ℝ F) (hfinite : K.faces.Finite)
    (dim : Finset F → ℕ)
    (hdim : ∀ s ∈ K.faces, ∀ t ∈ K.faces, t ⊂ s →
      (S ∩ intrinsicInterior ℝ (convexHull ℝ (s : Set F))).Nonempty →
      (S ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set F))).Nonempty →
      dim t < dim s)
    (hmaps : ∀ s ∈ K.faces,
      (S ∩ intrinsicInterior ℝ (convexHull ℝ (s : Set F))).Nonempty →
      ∃ e : PartialEquiv (Fin (dim s) → ℝ) F,
        e.source = ball 0 1 ∧
        e.target = S ∩ intrinsicInterior ℝ (convexHull ℝ (s : Set F)) ∧
        ContinuousOn e (closedBall 0 1) ∧
        ContinuousOn e.symm e.target ∧
        e '' closedBall 0 1 = S ∩ convexHull ℝ (s : Set F) ∧
        e '' sphere 0 1 = S ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set F))) :
    CWComplex (S ∩ K.space) := by
  classical
  let : Finite K.faces := hfinite.to_subtype
  let active := {s : K.faces //
    (S ∩ intrinsicInterior ℝ (convexHull ℝ (s.val : Set F))).Nonempty}
  let cell : ℕ → Type u := fun n => {s : active // dim s.val.val = n}
  have hexists (n : ℕ) (s : cell n) :
      ∃ e : PartialEquiv (Fin n → ℝ) F,
        e.source = ball 0 1 ∧
        e.target = S ∩ intrinsicInterior ℝ (convexHull ℝ (s.val.val.val : Set F)) ∧
        ContinuousOn e (closedBall 0 1) ∧
        ContinuousOn e.symm e.target ∧
        e '' closedBall 0 1 = S ∩ convexHull ℝ (s.val.val.val : Set F) ∧
        e '' sphere 0 1 = S ∩ intrinsicFrontier ℝ
          (convexHull ℝ (s.val.val.val : Set F)) := by
    rcases s with ⟨⟨⟨s, hs⟩, hactive⟩, hdegree⟩
    change dim s = n at hdegree
    subst n
    exact hmaps s hs hactive
  choose f hsrc htgt hcont hinv hclosed hfront using hexists
  have hfinite_cell (n : ℕ) : _root_.Finite (cell n) := inferInstance
  have heventually : ∀ᶠ n in Filter.atTop, IsEmpty (cell n) := by
    refine Filter.eventually_atTop.mpr
      ⟨hfinite.toFinset.sup dim + 1, fun n hn => ⟨fun s => ?_⟩⟩
    have hbound : dim s.val.val.val ≤ hfinite.toFinset.sup dim :=
      Finset.le_sup (hfinite.mem_toFinset.mpr s.val.val.property)
    have hdegree := s.property
    change dim s.val.val.val = n at hdegree
    omega
  have hopen (n : ℕ) (s : cell n) : f n s '' ball 0 1 =
      S ∩ intrinsicInterior ℝ (convexHull ℝ (s.val.val.val : Set F)) := by
    rw [← hsrc n s, (f n s).image_source_eq_target, htgt n s]
  refine CWComplex.mkFinite (S ∩ K.space) cell f heventually hfinite_cell
    (fun n s => hsrc n s) (fun n s => hcont n s) (fun n s => hinv n s) ?_ ?_ ?_
  · intro ⟨n, s⟩ _ ⟨m, t⟩ _ hne
    change Disjoint (f n s '' ball 0 1) (f m t '' ball 0 1)
    rw [hopen, hopen]
    have hd : Disjoint
        (intrinsicInterior ℝ (convexHull ℝ (s.val.val.val : Set F)))
        (intrinsicInterior ℝ (convexHull ℝ (t.val.val.val : Set F))) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have hintersection : x ∈ convexHull ℝ
          ((s.val.val.val ∩ t.val.val.val : Finset F) : Set F) := by
        rw [Finset.coe_inter]
        exact K.inter_subset_convexHull s.val.val.property t.val.val.property
          ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hy⟩
      by_cases hst : s.val.val.val ⊆ t.val.val.val
      · have hproper : s.val.val.val ∩ t.val.val.val ⊂ t.val.val.val := by
          rw [Finset.inter_eq_left.mpr hst]
          exact lt_of_le_of_ne hst (fun heq => hne (by
            have heq' : s.val = t.val := Subtype.ext (Subtype.ext heq)
            have hnm : n = m := by
              have hs := s.property
              have ht := t.property
              rw [heq'] at hs
              exact hs.symm.trans ht
            subst m
            exact congrArg (Sigma.mk n) (Subtype.ext heq')))
        exact Set.disjoint_left.mp (simplex_intrinsicInterior_disjoint_face
          t.val.val.val (s.val.val.val ∩ t.val.val.val)
          (K.nonempty_of_mem_faces t.val.val.property) (K.indep t.val.val.property)
          hproper) hy hintersection
      · have hproper : s.val.val.val ∩ t.val.val.val ⊂ s.val.val.val := by
          refine lt_of_le_of_ne Finset.inter_subset_left ?_
          intro heq
          exact hst (heq ▸ Finset.inter_subset_right)
        exact Set.disjoint_left.mp (simplex_intrinsicInterior_disjoint_face
          s.val.val.val (s.val.val.val ∩ t.val.val.val)
          (K.nonempty_of_mem_faces s.val.val.property) (K.indep s.val.val.property)
          hproper) hx hintersection
    exact hd.mono inter_subset_right inter_subset_right
  · intro n s x hx
    have hy : f n s x ∈ S ∩
        intrinsicFrontier ℝ (convexHull ℝ (s.val.val.val : Set F)) := by
      rw [← hfront n s]
      exact mem_image_of_mem (f n s) hx
    have hyfront := hy.2
    rw [simplex_intrinsicFrontier s.val.val.val
      (K.nonempty_of_mem_faces s.val.val.property) (K.indep s.val.val.property)] at hyfront
    obtain ⟨i, hix⟩ := mem_iUnion.mp hyfront
    obtain ⟨t, hts, htne, htx⟩ := exists_simplex_face_intrinsicInterior
      (s.val.val.val.erase (i : F))
      (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨f n s x, hix⟩))
      ((K.indep s.val.val.property).mono (Finset.erase_subset _ _)) hix
    have htproper : t ⊂ s.val.val.val :=
      Finset.ssubset_of_subset_of_ssubset hts (Finset.erase_ssubset i.property)
    have htface : t ∈ K.faces := K.down_closed s.val.val.property htproper.subset htne
    have htactive : (S ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set F))).Nonempty :=
      ⟨f n s x, hy.1, htx⟩
    let jactive : active := ⟨⟨t, htface⟩, htactive⟩
    let j : cell (dim t) := ⟨jactive, rfl⟩
    have hmn : dim t < n := by
      have hlt := hdim s.val.val.val s.val.val.property t htface htproper
        s.val.property htactive
      rwa [s.property] at hlt
    refine mem_iUnion.mpr ⟨dim t, mem_iUnion.mpr ⟨hmn,
      mem_iUnion.mpr ⟨j, ?_⟩⟩⟩
    rw [hclosed]
    exact ⟨hy.1, intrinsicInterior_subset htx⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hn
      rw [hclosed] at hs
      exact ⟨hs.1, K.convexHull_subset_space s.val.val.property hs.2⟩
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.2
      obtain ⟨t, hts, htne, htx⟩ := exists_simplex_face_intrinsicInterior s
        (K.nonempty_of_mem_faces hs) (K.indep hs) hxs
      have htface : t ∈ K.faces := K.down_closed hs hts htne
      let jactive : active := ⟨⟨t, htface⟩, ⟨x, hx.1, htx⟩⟩
      let j : cell (dim t) := ⟨jactive, rfl⟩
      refine mem_iUnion.mpr ⟨dim t, mem_iUnion.mpr ⟨j, ?_⟩⟩
      rw [hclosed]
      exact ⟨hx.1, intrinsicInterior_subset htx⟩

end PoincareConjecture.Proofs.M02
