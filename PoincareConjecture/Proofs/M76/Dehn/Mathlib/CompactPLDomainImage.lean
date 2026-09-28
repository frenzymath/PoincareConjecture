import PoincareConjecture.Proofs.M76.Mathlib.CompatibleChartPLMaps
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLImageNeighborhood













set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E G : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

omit [T2Space M] [FiniteDimensional ℝ G] in
private theorem exists_local_halfspace_image_pair
    {N : Set M} {F : M → G} (hinj : InjOn F N)
    (B : OpenPartialHomeomorph M E) (psi : E →ᴬ[ℝ] ℝ)
    (hpsi : psi.toAffineMap.linear ≠ 0)
    (hBN : ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y))
    (hF : LocallyPiecewiseAffineOn (F ∘ B.symm) B.target)
    {x : M} (hxB : x ∈ B.source) :
    ∃ (U D : Set M) (K L : SimplicialComplex ℝ G),
      IsOpen U ∧ x ∈ U ∧ D ⊆ N ∧ U ∩ N ⊆ D ∧
      K.faces.Finite ∧ L.faces.Finite ∧
      K.space = F '' D ∧ L.space = F '' (D ∩ frontier N) := by
  classical
  obtain ⟨J, hJ, hxJ, hJt, hFJ⟩ := hF (B x) (B.mapsTo hxB)
  let A : E →ᵃ[ℝ] ℝ := psi.toAffineMap
  let cuts : Finset (E →ᵃ[ℝ] ℝ) := {A, -A}
  let n := hJ.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ J.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hJ.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨T, hT, hTJ, _, hcuts⟩ :=
    J.exists_subdivision_respectsAffineHyperplanes hJ hn cuts
  let P := T.affineHalfspaceSubcomplex {-A}
  let Z := T.affineHalfspaceSubcomplex cuts
  have hP : P.faces.Finite := T.affineHalfspaceSubcomplex_finite {-A} hT
  have hZ : Z.faces.Finite := T.affineHalfspaceSubcomplex_finite cuts hT
  have hPspace : P.space = T.space ∩ {y | 0 ≤ psi y} := by
    rw [T.affineHalfspaceSubcomplex_space {-A} (by
      intro a ha
      rcases Finset.mem_singleton.mp ha with rfl
      exact hcuts (-A) (by simp [cuts]))]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
    change (y ∈ T.space ∧ -psi y ≤ 0) ↔ (y ∈ T.space ∧ 0 ≤ psi y)
    rw [neg_nonpos]
  have hZspace : Z.space = T.space ∩ {y | psi y = 0} := by
    rw [T.affineHalfspaceSubcomplex_space cuts hcuts]
    ext y
    simp only [cuts, mem_inter_iff, mem_ofPred_eq, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    change (y ∈ T.space ∧ psi y ≤ 0 ∧ -psi y ≤ 0) ↔
      (y ∈ T.space ∧ psi y = 0)
    rw [neg_nonpos]
    exact and_congr_right fun _ => ⟨fun h => le_antisymm h.1 h.2,
      fun h => ⟨h.le, h.ge⟩⟩
  have hPt : P.space ⊆ B.target := by
    rw [hPspace, hTJ.space_eq]
    exact inter_subset_left.trans hJt
  have hZP : Z.space ⊆ P.space := by
    rw [hZspace, hPspace]
    exact fun _ hy => ⟨hy.1, hy.2.ge⟩
  have hmapN : MapsTo B.symm P.space N := by
    intro y hy
    apply (hBN (B.symm y) (B.symm.mapsTo (hPt hy))).mpr
    rw [B.right_inv (hPt hy)]
    exact (hPspace ▸ hy).2
  have hinjP : InjOn (F ∘ B.symm) P.space := by
    intro y hy z hz hyz
    exact B.symm.injOn (hPt hy) (hPt hz) (hinj (hmapN hy) (hmapN hz) hyz)
  have hFT : T.AffineOnFaces (F ∘ B.symm) := hTJ.affineOnFaces hFJ
  have hFP : P.AffineOnFaces (F ∘ B.symm) := fun s hs => hFT s hs.1
  have hFZ : Z.AffineOnFaces (F ∘ B.symm) := fun s hs => hFT s hs.1
  let D : Set M := B.symm '' P.space
  let U : Set M := B.source ∩ B ⁻¹' interior J.space
  have hU : IsOpen U :=
    B.continuousOn.isOpen_inter_preimage B.open_source isOpen_interior
  have hUN : U ∩ N ⊆ D := by
    intro y hy
    refine ⟨B y, ?_, B.left_inv hy.1.1⟩
    rw [hPspace, hTJ.space_eq]
    exact ⟨interior_subset hy.1.2, (hBN y hy.1.1).mp hy.2⟩
  have hfront := B.isImage_frontier_of_affine_nonneg psi hpsi hBN
  have hDfront : B.symm '' Z.space = D ∩ frontier N := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hZP hz, rfl⟩, ?_⟩
      exact (hfront.symm_apply_mem_iff (hPt (hZP hz))).mpr ((hZspace ▸ hz).2)
    · rintro ⟨⟨z, hz, rfl⟩, hzfront⟩
      refine ⟨z, ?_, rfl⟩
      rw [hZspace]
      exact ⟨(hPspace ▸ hz).1, (hfront.symm_apply_mem_iff (hPt hz)).mp hzfront⟩
  refine ⟨U, D, hFP.embeddedImage hinjP, hFZ.embeddedImage (hinjP.mono hZP),
    hU, ⟨hxB, hxJ⟩, ?_, hUN, hFP.embeddedImage_finite hinjP hP,
    hFZ.embeddedImage_finite (hinjP.mono hZP) hZ, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hmapN hy
  · rw [hFP.embeddedImage_space]
    exact (image_image F B.symm P.space).symm
  · rw [hFZ.embeddedImage_space]
    exact (image_image F B.symm Z.space).symm.trans
      (congrArg (fun Q : Set M => F '' Q) hDfront)

omit [T2Space M] [FiniteDimensional ℝ G] in
private theorem exists_local_interior_image_pair
    {N : Set M} {F : M → G} (hinj : InjOn F N)
    (B : OpenPartialHomeomorph M E)
    (hF : LocallyPiecewiseAffineOn (F ∘ B.symm) B.target)
    {x : M} (hxB : x ∈ B.source) (hxN : x ∈ interior N) :
    ∃ (U D : Set M) (K L : SimplicialComplex ℝ G),
      IsOpen U ∧ x ∈ U ∧ D ⊆ N ∧ U ∩ N ⊆ D ∧
      K.faces.Finite ∧ L.faces.Finite ∧
      K.space = F '' D ∧ L.space = F '' (D ∩ frontier N) := by
  classical
  obtain ⟨J, hJ, hxJ, _, hFJ⟩ := hF (B x) (B.mapsTo hxB)
  let V : Set E := B.target ∩ B.symm ⁻¹' interior N
  have hV : IsOpen V :=
    B.symm.continuousOn.isOpen_inter_preimage B.open_target isOpen_interior
  have hxV : B x ∈ V := by
    refine ⟨B.mapsTo hxB, ?_⟩
    change B.symm (B x) ∈ interior N
    rw [B.left_inv hxB]
    exact hxN
  obtain ⟨T, hT, hxT, hTV, hFT⟩ := hFJ.exists_finite_neighborhood hJ
    (isCompact_singleton (x := B x)) hV (singleton_subset_iff.mpr ⟨hxJ, hxV⟩)
  have hTt : T.space ⊆ B.target := fun _ hy => (hTV hy).2.1
  have hTNi : MapsTo B.symm T.space (interior N) := fun _ hy => (hTV hy).2.2
  have hinjT : InjOn (F ∘ B.symm) T.space := by
    intro y hy z hz hyz
    exact B.symm.injOn (hTt hy) (hTt hz)
      (hinj (interior_subset (hTNi hy)) (interior_subset (hTNi hz)) hyz)
  let D : Set M := B.symm '' T.space
  let U : Set M := B.source ∩ B ⁻¹' interior T.space
  have hU : IsOpen U :=
    B.continuousOn.isOpen_inter_preimage B.open_source isOpen_interior
  have hDNi : D ⊆ interior N := by
    rintro _ ⟨y, hy, rfl⟩
    exact hTNi hy
  have hDfront : D ∩ frontier N = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact disjoint_left.mp disjoint_interior_frontier (hDNi hy.1) hy.2
  refine ⟨U, D, hFT.embeddedImage hinjT, ⊥, hU,
    ⟨hxB, hxT (mem_singleton _)⟩, hDNi.trans interior_subset, ?_,
    hFT.embeddedImage_finite hinjT hT, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨B y, interior_subset hy.1.2, B.left_inv hy.1.1⟩
  · exact Set.finite_empty
  · rw [hFT.embeddedImage_space]
    exact (image_image F B.symm T.space).symm
  · rw [SimplicialComplex.space_bot, hDfront, image_empty]






theorem exists_finite_triangulations_domain_frontier_image
    {ι : Type*} (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {F : M → G} (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    {N : Set M} (hN : IsCompact N) (hinj : InjOn F N)
    (hboundary : ∀ x ∈ frontier N,
      ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y)) :
    ∃ K L : SimplicialComplex ℝ G, K.faces.Finite ∧ L.faces.Finite ∧
      K.space = F '' N ∧ L.space = F '' frontier N := by
  classical
  have hlocal (x : N) :
      ∃ (U D : Set M) (K L : SimplicialComplex ℝ G),
        IsOpen U ∧ (x : M) ∈ U ∧ D ⊆ N ∧ U ∩ N ⊆ D ∧
        K.faces.Finite ∧ L.faces.Finite ∧
        K.space = F '' D ∧ L.space = F '' (D ∩ frontier N) := by
    by_cases hx : (x : M) ∈ frontier N
    · obtain ⟨psi, v, B, hnorm, hxB, _, hBPL, hBN⟩ := hboundary x hx
      have hpsi : psi.toAffineMap.linear ≠ 0 := by
        intro hzero
        have hv : psi.toAffineMap.linear v = 1 := hnorm
        rw [hzero, LinearMap.zero_apply] at hv
        exact zero_ne_one hv
      exact exists_local_halfspace_image_pair hinj B psi hpsi hBN
        (locallyPiecewiseAffineOn_compatible_chart e hcover hF B hBPL) hxB
    · obtain ⟨i, hxi⟩ := hcover x
      exact exists_local_interior_image_pair hinj (e i) (hF i) hxi
        ((mem_interior_iff_notMem_frontier x.property).mpr hx)
  choose U D K L hU hxU hDN hUD hK hL hKD hLD using hlocal
  obtain ⟨s, hs⟩ := hN.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hDcover : (⋃ a : s, D a) = N := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
      exact hDN a hxa
    · intro x hx
      obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨a, has⟩, hUD a ⟨hxa, hx⟩⟩
  obtain ⟨K', hK', hKs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun a : s => K a) (fun a => hK a)
  obtain ⟨L', hL', hLs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun a : s => L a) (fun a => hL a)
  refine ⟨K', L', hK', hL', ?_, ?_⟩
  · rw [hKs]
    simp_rw [hKD]
    rw [← image_iUnion, hDcover]
  · rw [hLs]
    simp_rw [hLD]
    rw [← image_iUnion, ← iUnion_inter, hDcover,
      inter_eq_self_of_subset_right hN.isClosed.frontier_subset]

end OpenPartialHomeomorph
