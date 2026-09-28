import PoincareConjecture.Proofs.M76.Mathlib.CompactPLNeighborhoodModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalDomainCharts
import PoincareConjecture.Proofs.M76.Rigidity.CompatibleChartPatch
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLEqualityLoci

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

private theorem original_region_traces
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) :
    ∃ P B : SimplicialComplex ℝ E, P.faces.Finite ∧ B.faces.Finite ∧
      P.space = K.space ∩ g ⁻¹' R ∧ B.space = K.space ∩ g ⁻¹' frontier R := by
  classical
  have hchart (x : K.space) : ∃ Q : OpenPartialHomeomorph X V3,
      g x ∈ Q.source ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (Q.source ⊆ interior R ∨ Q.source ⊆ Rᶜ ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          ∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y)) := by
    by_cases hx : g x ∈ R
    · obtain ⟨Q, hxQ, hQ, hkind⟩ := he.exists_local_region_chart ⟨g x, hx⟩
      refine ⟨Q, hxQ, hQ, ?_⟩
      rcases hkind with hin | ⟨ell, v, hv, _, hhalf⟩
      · exact Or.inl (interior_maximal hin Q.open_source)
      · exact Or.inr (Or.inr ⟨ell, v, hv, hhalf⟩)
    · obtain ⟨i, hi⟩ := he.cover (g x)
      let Q := (e i).restrOpen Rᶜ he.closed.isOpen_compl
      refine ⟨Q, ⟨hi, hx⟩, ?_, Or.inr (Or.inl (fun _ hy => hy.2))⟩
      intro j
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (he.compatible j i)).mono
        ((e j).symm.trans Q).open_source (fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hlocal (x : K.space) :
      ∃ (N P B : SimplicialComplex ℝ E) (W : Set K.space),
        N.space ⊆ K.space ∧ IsOpen W ∧ x ∈ W ∧ Subtype.val '' W ⊆ N.space ∧
        P.faces.Finite ∧ B.faces.Finite ∧
        P.space = N.space ∩ g ⁻¹' R ∧ B.space = N.space ∩ g ⁻¹' frontier R := by
    obtain ⟨Q, hxQ, hQ, hkind⟩ := hchart x
    obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNQ, hcoords⟩ :=
      hg.exists_finite_compatible_chart_patch K hK Q hQ x hxQ
    have hbot : (⊥ : SimplicialComplex ℝ E).faces.Finite := by
      rw [SimplicialComplex.faces_bot]
      exact finite_empty
    rcases hkind with hin | hout | ⟨ell, v, hv, hhalf⟩
    · refine ⟨N, N, ⊥, W, hNK, hW, hxW, hWN, hN, hbot, ?_, ?_⟩
      · apply Subset.antisymm
        · intro z hz
          exact ⟨hz, show g z ∈ R from interior_subset (hin (hNQ hz))⟩
        · exact inter_subset_left
      · rw [SimplicialComplex.space_bot]
        apply Eq.symm
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact disjoint_left.mp disjoint_interior_frontier (hin (hNQ hz.1)) hz.2
    · refine ⟨N, ⊥, ⊥, W, hNK, hW, hxW, hWN, hbot, hbot, ?_, ?_⟩
      · rw [SimplicialComplex.space_bot]
        apply Eq.symm
        exact eq_empty_iff_forall_notMem.mpr (fun z hz => hout (hNQ hz.1) hz.2)
      · rw [SimplicialComplex.space_bot]
        apply Eq.symm
        exact eq_empty_iff_forall_notMem.mpr
          (fun z hz => hout (hNQ hz.1) (he.closed.frontier_subset hz.2))
    · let a : V3 →ᵃ[ℝ] ℝ := ell.toAffineMap
      obtain ⟨P, hP, hPs⟩ := hcoords.exists_finite_halfspace_preimage {-a}
      obtain ⟨B, hB, hBs⟩ := hcoords.exists_finite_halfspace_preimage {a, -a}
      have ha : ell.toAffineMap.linear ≠ 0 := by
        intro hz
        have hzero : ell.contLinear v = 0 := congrFun (congrArg DFunLike.coe hz) v
        exact zero_ne_one (hzero.symm.trans hv)
      have hfront := Q.isImage_frontier_of_affine_nonneg ell ha hhalf
      refine ⟨N, P, B, W, hNK, hW, hxW, hWN, hP, hB, ?_, ?_⟩
      · rw [hPs]
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton, forall_eq,
          mem_preimage]
        change (z ∈ N.space ∧ -ell (Q (g z)) ≤ 0) ↔ (z ∈ N.space ∧ g z ∈ R)
        exact and_congr_right fun hz => by rw [neg_nonpos, hhalf _ (hNQ hz)]
      · rw [hBs]
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
          forall_eq_or_imp, forall_eq, mem_preimage]
        change (z ∈ N.space ∧ ell (Q (g z)) ≤ 0 ∧ -ell (Q (g z)) ≤ 0) ↔
          (z ∈ N.space ∧ g z ∈ frontier R)
        apply and_congr_right
        intro hz
        rw [neg_nonpos, ← hfront.apply_mem_iff (hNQ hz)]
        exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  choose N P B W hNK hW hxW hWN hP hB hPs hBs using hlocal
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  obtain ⟨P0, hP0, hP0s, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun x : t => P x) (fun x => hP x)
  obtain ⟨B0, hB0, hB0s, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun x : t => B x) (fun x => hB x)
  have hunion (J : K.space → SimplicialComplex ℝ E) (Z : Set X)
      (hJ : ∀ x, (J x).space = (N x).space ∩ g ⁻¹' Z) :
      (⋃ x : t, (J x).space) = K.space ∩ g ⁻¹' Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp hz
      rw [hJ x] at hx
      exact ⟨hNK x hx.1, hx.2⟩
    · intro hz
      obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp (ht (mem_univ (⟨z, hz.1⟩ : K.space)))
      refine mem_iUnion.mpr ⟨⟨x, hxt⟩, ?_⟩
      rw [hJ x]
      exact ⟨hWN x (mem_image_of_mem Subtype.val hx), hz.2⟩
  exact ⟨P0, B0, hP0, hB0, hP0s.trans (hunion P R hPs),
    hB0s.trans (hunion B (frontier R) hBs)⟩

private theorem complete_finite_source_clip
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : Set E} {f : E → F}
    (hf : FinitePiecewiseAffineOn f S)
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧ T.space = S ∩ f ⁻¹' K.space := by
  classical
  let : Finite K.faces := hK.to_subtype
  have hpiece (s : K.faces) : ∃ T : SimplicialComplex ℝ E,
      T.faces.Finite ∧ T.space = S ∩ f ⁻¹' convexHull ℝ (s.val : Set F) := by
    obtain ⟨cuts, hcuts⟩ := s.val.exists_affine_halfspaces_convexHull (K.indep s.property)
    obtain ⟨T, hT, hTs⟩ := hf.exists_finite_halfspace_preimage cuts
    refine ⟨T, hT, hTs.trans ?_⟩
    rw [hcuts]
    rfl
  choose T hT hTs using hpiece
  obtain ⟨L, hL, hLs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion T hT
  refine ⟨L, hL, hLs.trans ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs⟩ := mem_iUnion.mp hz
    rw [hTs s] at hs
    exact ⟨hs.1, K.convexHull_subset_space s.property hs.2⟩
  · intro hz
    obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp hz.2
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, (hTs ⟨s, hs⟩).symm ▸ ⟨hz.1, hzs⟩⟩

open Classical in

theorem exists_original_signed_tube_model
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    {A O : Set X} (hA : IsCompact A) (hne : A.Nonempty)
    (hO : IsOpen O) (hAO : A ⊆ O)
    (E : κ → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (P : ∀ i, SimplicialComplex ℝ (E i)) (hP : ∀ i, (P i).faces.Finite)
    (f : ∀ i, E i → X) (hf : ∀ i, PolyhedralPLInCharts e (f i) (P i).space) :
    ∃ (s : Finset A) (F : X → (s → ℝ × V3)) (C : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (M : Sum Bool κ → SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C)
      (T : ∀ i, SimplicialComplex ℝ (E i)),
      IsCompact C ∧ A ⊆ interior C ∧ C ⊆ O ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ C, ∀ y : X, F x = F y → x = y) ∧ K.faces.Finite ∧
      (∀ i, M i ≤ K ∧ (M i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces) ∧
      K.space = F '' C ∧
      (M (.inl false)).space = F '' (C ∩ R) ∧
      (M (.inl true)).space = F '' (C ∩ frontier R) ∧
      (∀ i, (M (.inr i)).space = F '' (C ∩ (f i '' (P i).space))) ∧
      (∀ i, (T i).faces.Finite ∧ (T i).space = (P i).space ∩ (f i) ⁻¹' C ∧
        FinitePiecewiseAffineOn (F ∘ f i) (T i).space ∧
        (F ∘ f i) '' (T i).space = (M (.inr i)).space) ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      ∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨s, c, Q, F, _, hQe, hAQ, hFc, hF, hproj, hsep⟩ :=
    OpenPartialHomeomorph.exists_locallyPL_graph_separating_compact_core
      e he.compatible he.cover hA hO hAO
  let V : Set X := ⋃ i, interior (Q i)
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_interior)
  have hVQ : V ⊆ ⋃ i, Q i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, interior_subset hxi⟩
  have hVO : V ⊆ O := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hVQ hx)
    exact (hQe i hxi).2
  have hinj : InjOn F V := fun x hx _ _ hxy => hsep x (hVQ hx) _ hxy
  obtain ⟨C, K0, H0, hC, hAC, hCV, hK0, _, hHF⟩ :=
    OpenPartialHomeomorph.exists_compact_finitePL_image_neighborhood
      e F hFc he.cover hF hA hV hAQ hinj
  have hseparate : ∀ x ∈ C, ∀ y : X, F x = F y → x = y :=
    fun x hx => hsep x (hVQ (hCV hx))
  have hprojections (x : X) (hx : x ∈ C) :
      ∃ (i : ι) (U : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen U ∧ x ∈ U ∧ U ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) U := by
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hCV hx)
    let a : (s → ℝ × V3) →ᴬ[ℝ] V3 :=
      ((ContinuousLinearMap.snd ℝ ℝ V3).comp (ContinuousLinearMap.proj i)).toContinuousAffineMap
    exact ⟨c i, interior (Q i), a, isOpen_interior, hxi,
      fun y hy => (hQe i (interior_subset hy)).1,
      fun y hy => congrArg Prod.snd (hproj i (interior_subset hy))⟩
  obtain ⟨x0, hx0⟩ := hne
  let z0 : C := ⟨x0, interior_subset (hAC hx0)⟩
  obtain ⟨g, hgc, hg, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K0 hK0 H0 F (Subset.refl C) z0 hHF hprojections
  have hK0s : K0.space = F '' C := by
    apply Subset.antisymm
    · intro z hz
      refine ⟨H0.symm ⟨z, hz⟩, (H0.symm ⟨z, hz⟩).property, ?_⟩
      exact (hHF (H0.symm ⟨z, hz⟩)).symm.trans
        (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hHF ⟨x, hx⟩]
      exact (H0 ⟨x, hx⟩).property
  have hFmem (x : X) : F x ∈ K0.space ↔ x ∈ C := by
    rw [hK0s]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact hseparate y hy x hyx ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  obtain ⟨P0, B0, hP0, hB0, hP0s, hB0s⟩ :=
    original_region_traces he K0 hK0 hgPL
  have htrace (Z : Set X) : K0.space ∩ (fun z => (g z : X)) ⁻¹' Z = F '' (C ∩ Z) := by
    ext z
    constructor
    · intro hz
      refine ⟨g z, ⟨(g z).property, hz.2⟩, ?_⟩
      have h := congrArg F (hg ⟨z, hz.1⟩)
      exact h.trans ((hHF (H0.symm ⟨z, hz.1⟩)).symm.trans
        (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz.1⟩)))
    · rintro ⟨x, hx, rfl⟩
      have hxK := (hFmem x).mpr hx.1
      refine ⟨hxK, ?_⟩
      have h := hg (H0 ⟨x, hx.1⟩)
      have hgFx : (g (F x) : X) = x := by
        simpa only [hHF, H0.symm_apply_apply] using h
      change (g (F x) : X) ∈ Z
      rw [hgFx]
      exact hx.2
  have hmarks (i : κ) : ∃ (T : SimplicialComplex ℝ (E i))
      (J : SimplicialComplex ℝ (s → ℝ × V3)),
      T.faces.Finite ∧ T.space = (P i).space ∩ (f i) ⁻¹' C ∧
      FinitePiecewiseAffineOn (F ∘ f i) T.space ∧ J.faces.Finite ∧
      J.space = (F ∘ f i) '' T.space ∧ J.space = F '' (C ∩ (f i '' (P i).space)) := by
    have hcoords := (hf i).finitePiecewiseAffineOn_comp (P i) (hP i) hF
    obtain ⟨T, hT, hTs⟩ := complete_finite_source_clip hcoords K0 hK0
    have hTs' : T.space = (P i).space ∩ (f i) ⁻¹' C := by
      rw [hTs]
      ext z
      exact and_congr_right fun _ => hFmem (f i z)
    have hTsub : T.space ⊆ (P i).space := hTs'.subset.trans inter_subset_left
    have hFT := hcoords.restrict T hT hTsub
    obtain ⟨J, hJ, hJs⟩ := hFT.exists_finite_triangulation_image
    refine ⟨T, J, hT, hTs', hFT, hJ, hJs, hJs.trans ?_⟩
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hTs'] at hy
      exact ⟨f i y, ⟨hy.2, ⟨y, hy.1, rfl⟩⟩, rfl⟩
    · rintro ⟨x, ⟨hxC, y, hy, hyx⟩, hFx⟩
      have hyC : f i y ∈ C := hyx.symm ▸ hxC
      refine ⟨y, hTs'.symm ▸ ⟨hy, hyC⟩, ?_⟩
      exact (congrArg F hyx).trans hFx
  choose T J hT hTs hFT hJ hJs hJimage using hmarks
  let marks : Sum Bool κ → SimplicialComplex ℝ (s → ℝ × V3) :=
    Sum.elim (fun b => if b then B0 else P0) J
  have hmarksfin : ∀ i, (marks i).faces.Finite := by
    intro i
    rcases i with b | i
    · cases b <;> assumption
    · exact hJ i
  have hmarkssub : ∀ i, (marks i).space ⊆ K0.space := by
    intro i
    rcases i with b | i
    · cases b
      · change P0.space ⊆ K0.space
        exact hP0s.subset.trans inter_subset_left
      · change B0.space ⊆ K0.space
        exact hB0s.subset.trans inter_subset_left
    · change (J i).space ⊆ K0.space
      rw [hJimage, hK0s]
      exact image_mono inter_subset_left
  obtain ⟨K, M, hK, hKK0, hM⟩ :=
    K0.exists_subdivision_with_finite_full_polyhedra hK0 marks hmarksfin hmarkssub
  let H : C ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  refine ⟨s, F, C, K, M, H, g, T, hC, hAC, hCV.trans hVO, hFc, hF,
    hseparate, hK, ?_, hKK0.space_eq.trans hK0s, ?_, ?_, ?_, ?_, hHF,
    hKK0.space_eq.symm ▸ hgc, ?_, hKK0.space_eq.symm ▸ hgPL, hprojections⟩
  · exact fun i => ⟨(hM i).1, hK.subset (hM i).1, (hM i).2.2⟩
  · exact (hM (.inl false)).2.1.trans (hP0s.trans (htrace R))
  · exact (hM (.inl true)).2.1.trans (hB0s.trans (htrace (frontier R)))
  · exact fun i => (hM (.inr i)).2.1.trans (hJimage i)
  · exact fun i => ⟨hT i, hTs i, hFT i, (hJs i).symm.trans (hM (.inr i)).2.1.symm⟩
  · exact fun z => hg ⟨z, hKK0.space_eq.subset z.property⟩

end PoincareConjecture.M76.Dehn
