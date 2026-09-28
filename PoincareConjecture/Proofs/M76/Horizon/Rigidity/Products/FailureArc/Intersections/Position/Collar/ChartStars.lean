import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_collar_adapted_original_chart_stars
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K M : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hM : M.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (mark : Set X) (hmark : IsClosed mark)
    {z : E → ℝ} (hz : Continuous z) {c : ℝ} (hc : 0 < c)
    (hMs : M.space = K.space ∩ {x | z x ≤ c})
    (hzero : ∀ x ∈ K.space, g x ∈ mark → z x = 0) :
    ∃ (R L : SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧ L ≤ R ∧ L.space = M.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) ∧
      (∀ p ∈ R.vertices, ∃ B : OpenPartialHomeomorph X (Fin 3 → ℝ),
        MapsTo g (R.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
        (R.closedStar p).AffineOnFaces (B ∘ g)) ∧
      ∀ s ∈ R.faces, s ∉ L.faces →
        ∃ (B : OpenPartialHomeomorph X (Fin 3 → ℝ)) (A : E →ᴬ[ℝ] (Fin 3 → ℝ)),
          (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
          Disjoint B.source mark ∧ MapsTo g (convexHull ℝ (s : Set E)) B.source ∧
          EqOn (B ∘ g) A (convexHull ℝ (s : Set E)) := by
  classical
  let core : Set E := K.space ∩ {x | c ≤ z x}
  have hcore : IsCompact core :=
    (K.isCompact_space_of_finite hK).inter_right (isClosed_Ici.preimage hz)
  have hphysicalCore : IsClosed (g '' core) :=
    (hcore.image_of_continuousOn (hg.continuousOn.mono inter_subset_left)).isClosed
  have hpoint (q : K.space) : ∃ i, g q ∈ (e i).source := by
    obtain ⟨i, P, U, _, _, _, hqU, hUP, hPe, _⟩ := hg.coordinates q
    exact ⟨i, hPe (hUP (mem_image_of_mem Subtype.val hqU))⟩
  choose index hindex using hpoint
  let O (q : K.space) : Set X := if g q ∈ mark then (g '' core)ᶜ else markᶜ
  have hO (q : K.space) : IsOpen (O q) := by
    unfold O
    split_ifs
    · exact hphysicalCore.isOpen_compl
    · exact hmark.isOpen_compl
  have hqO (q : K.space) : g q ∈ O q := by
    unfold O
    split_ifs with hq
    · rintro ⟨x, hx, heq⟩
      have hxq : x = q := hgi hx.1 q.property heq
      have hzc := hxq ▸ hx.2
      change c ≤ z q at hzc
      rw [hzero q q.property hq] at hzc
      exact hc.not_ge hzc
    · exact hq
  let B (q : K.space) := (e (index q)).restrOpen (O q) (hO q)
  have hB (q : K.space) (i : ι) : (e i).symm.trans (B q) ∈
      piecewiseAffineGroupoid (Fin 3 → ℝ) := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact (he i (index q)).1.mono ((e i).symm.trans (B q)).open_source
      (fun x hx => ⟨hx.1, hx.2.1⟩)
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    hg.exists_full_compatible_chart_stars K hK B hB
      (fun q => ⟨hindex q, hqO q⟩) (fun _ : Unit => M) (fun _ => hM)
      (fun _ => hMs.subset.trans inter_subset_left)
  obtain ⟨hLR, hLs, hfull⟩ := hL ()
  refine ⟨R, L (), hR, hRK, hLR, hLs, hfull, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hmap, hface⟩ := hstars p hp
    exact ⟨B q, hmap, hB q, hface⟩
  · intro s hs hsL
    obtain ⟨p, hp, hpL⟩ : ∃ p ∈ s, p ∉ (L ()).vertices := by
      by_contra hn
      push Not at hn
      exact hsL (hfull s hs hn)
    obtain ⟨q, hmap, hface⟩ := hstars p (R.face_subset_vertices hs hp)
    have hsstar : s ∈ (R.closedStar p).faces := ⟨hs, by simpa only [Finset.insert_eq_of_mem hp] using hs⟩
    obtain ⟨A, hA⟩ := hface s hsstar
    have hmapS := hmap.mono_left ((R.closedStar p).convexHull_subset_space hsstar)
    have hqnot : g q ∉ mark := by
      intro hq
      have hpK : p ∈ K.space := hRK.space_eq.subset
        (R.vertices_subset_space (R.face_subset_vertices hs hp))
      have hpM : p ∉ M.space := by
        intro hpM
        have hpLspace : p ∈ (L ()).space := hLs.symm.subset hpM
        obtain ⟨t, ht, hpt⟩ := SimplicialComplex.mem_space_iff.mp hpLspace
        have hptsub : ({p} : Finset E) ⊆ t :=
          R.subset_of_mem_intrinsicInterior_face (R.face_subset_vertices hs hp) (hLR ht)
            (by simp) hpt
        exact hpL ((L ()).down_closed ht hptsub (Finset.singleton_nonempty p))
      have hpc : c < z p := lt_of_not_ge (fun h => hpM (hMs.symm.subset ⟨hpK, h⟩))
      have hpB := hmapS (subset_convexHull ℝ _ hp)
      have hpn : g p ∉ g '' core := by
        have hh : g p ∈ O q := hpB.2
        simpa only [O, if_pos hq, mem_compl_iff] using hh
      exact hpn ⟨p, ⟨hpK, hpc.le⟩, rfl⟩
    refine ⟨B q, A, hB q, ?_, hmapS, hA⟩
    apply disjoint_left.mpr
    intro x hx hxmark
    have hh : x ∈ O q := hx.2
    exact (show x ∉ mark by simpa only [O, if_neg hqnot, mem_compl_iff] using hh) hxmark

end PoincareConjecture.M76
