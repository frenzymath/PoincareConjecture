import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalContactLineCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.ConvexCarrierWindow
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ChartCarrier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology

set_option autoImplicit false

open Set Geometry Module

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem member_subedge_contact_line_cover
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (sS : ChartwisePLSphere e S) (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (has : a ⊆ s) (ha2 : a.card = 2)
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {y : X} (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E))) :
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧
      (∀ B ∈ L, finrank ℝ B.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E))) ∩ U,
        ∃ B ∈ L, x ∈ B := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp ha2
  obtain ⟨w, hw, rfl⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨has, by rw [Finset.card_pair hpq, hs3]⟩
  have hwp : w ≠ p := fun he => hw (he.symm ▸ Finset.mem_insert_self _ _)
  have hwq : w ≠ q := fun he => hw (he.symm ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))
  simp only [Finset.coe_insert, Finset.coe_singleton] at hmap hA ⊢
  have hy' : y ∈ S ∩ (g '' segment ℝ p q) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hy
  obtain ⟨U, L, hU, hyU, _, hL, hcover⟩ :=
    h.exists_triangle_contact_line_cover_of_affine_chart sS hgi hSV hpq hwp hwq
      hs hy' Q hQ A hmap hA
  exact ⟨U, L, hU, hyU, hL, hcover⟩

theorem exists_sphere_system_chart_isolation
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (Q : OpenPartialHomeomorph X V3) (i : κ) {y : X}
    (hy : y ∈ S i) (hyQ : y ∈ Q.source) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ U, x ∈ Q '' ((⋃ j, S j) ∩ Q.source) ↔
        x ∈ Q '' (S i ∩ Q.source) := by
  obtain ⟨O, hO, hSiO, hOi, _⟩ := exists_open_sphere_system_isolation S sS hdis i
  refine ⟨Q.target ∩ Q.symm ⁻¹' O, Q.isOpen_inter_preimage_symm hO,
    ⟨Q.map_source hyQ, ?_⟩, inter_subset_left, ?_⟩
  · simpa only [mem_preimage, Q.left_inv hyQ] using hSiO hy
  · intro x hx
    constructor
    · rintro ⟨z, ⟨hzS, hzQ⟩, hzx⟩
      have hzO : z ∈ O := by
        have h := hx.2
        change Q.symm x ∈ O at h
        rwa [← hzx, Q.left_inv hzQ] at h
      exact ⟨z, ⟨hOi.subset ⟨hzO, hzS⟩, hzQ⟩, hzx⟩
    · rintro ⟨z, ⟨hzS, hzQ⟩, hzx⟩
      exact ⟨z, ⟨mem_iUnion.mpr ⟨i, hzS⟩, hzQ⟩, hzx⟩

private theorem sphere_system_subedge_contact_line_cover
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (hs : s ∈ K.faces) (hs3 : s.card = 3) (has : a ⊆ s) (ha2 : a.card = 2)
    (h : ∀ i, HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {y : X} (hy : y ∈ (⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))) :
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧
      (∀ B ∈ L, finrank ℝ B.direction ≤ 1) ∧
      ∀ x ∈ (Q '' ((⋃ i, S i) ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E))) ∩ U,
        ∃ B ∈ L, x ∈ B := by
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hy.1
  have hyQ : y ∈ Q.source := by
    obtain ⟨z, hz, rfl⟩ := hy.2
    exact hmap (convexHull_mono has hz)
  obtain ⟨O, hO, hyO, _, hOi⟩ := exists_sphere_system_chart_isolation S sS hdis Q i hyi hyQ
  obtain ⟨U, L, hU, hyU, hL, hcover⟩ := member_subedge_contact_line_cover
    (sS i) hs hs3 has ha2 (h i) hgi (hSV.mono_left (subset_iUnion S i))
    Q hQ A hmap hA ⟨hyi, hy.2⟩
  refine ⟨U ∩ O, L, hU.inter hO, ⟨hyU, hyO⟩, hL, ?_⟩
  rintro x ⟨⟨hxS, hxt⟩, hxU, hxO⟩
  exact hcover x ⟨⟨(hOi x hxO).mp hxS, hxt⟩, hxU⟩

theorem exists_original_sphere_system_triangle_protected_cover
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (K : SimplicialComplex ℝ E) (g : E → X)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ (t : Finset V3) (T J P : SimplicialComplex ℝ V3) (Z : Set V3),
      t = s.image A ∧ t.card = 3 ∧ T.faces.Finite ∧ t ∈ T.faces ∧
      T.space = convexHull ℝ (t : Set V3) ∧
      J.faces.Finite ∧ Convex ℝ J.space ∧ T.space ⊆ interior J.space ∧
      J.space ⊆ Q.target ∧ P.faces.Finite ∧
      P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space ∧
      (∀ a ∈ P.faces, a.card ≤ 3) ∧ Disjoint P.space T.vertices ∧
      (∀ a ∈ T.faces, a.card = 2 → (P.space ∩ convexHull ℝ (a : Set V3)).Finite) ∧
      Z = (⋃ a ∈ T.faces, ⋃ (_ : a.card = 2), convexHull ℝ (a : Set V3)) ∪
        frontier J.space ∧ IsClosed Z ∧ frontier J.space ⊆ Z ∧
      (∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set V3),
        ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
          ∃ L : Finset (AffineSubspace ℝ V3),
            (∀ B ∈ L, finrank ℝ B.direction ≤ 1) ∧
            ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ B ∈ L, y ∈ B) := by
  classical
  let K₀ : SimplicialComplex ℝ E :=
    { faces := {a | a ∈ K.faces ∧ a ⊆ s}
      indep := fun ha => K.indep ha.1
      isRelLowerSet_faces := by
        intro a ha
        exact ⟨K.nonempty_of_mem_faces ha.1, fun b hba hb =>
          ⟨K.down_closed ha.1 hba hb, hba.trans ha.2⟩⟩
      inter_subset_convexHull := fun ha hb => K.inter_subset_convexHull ha.1 hb.1 }
  have hK₀ : K₀.faces.Finite := s.powerset.finite_toSet.subset
    (fun _ ha => Finset.mem_powerset.mpr ha.2)
  have hs₀ : s ∈ K₀.faces := ⟨hs, Finset.Subset.rfl⟩
  have hK₀s : K₀.space = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact convexHull_mono ha.2 hxa
    · exact K₀.convexHull_subset_space hs₀
  have hAi : InjOn A K₀.space := by
    intro x hx y hy hxy
    have hx' := hK₀s.subset hx
    have hy' := hK₀s.subset hy
    apply hgi (K.convexHull_subset_space hs hx') (K.convexHull_subset_space hs hy')
    exact Q.injOn (hmap hx') (hmap hy') ((hA hx').trans (hxy.trans (hA hy').symm))
  have hf : K₀.AffineOnFaces A := K₀.affineOnFaces_affine A
  let T := hf.embeddedImage hAi
  let t := s.image A
  have hT : T.faces.Finite := hf.embeddedImage_finite hAi hK₀
  have ht : t ∈ T.faces := (hf.image_mem_embeddedImage_iff hAi (K₀.subset_space hs₀)).mpr hs₀
  have ht3 : t.card = 3 := (Finset.card_image_iff.mpr (hAi.mono (K₀.subset_space hs₀))).trans hs3
  have hTs : T.space = convexHull ℝ (t : Set V3) := by
    rw [hf.embeddedImage_space hAi, hK₀s]
    dsimp only [t]
    rw [Finset.coe_image]
    exact hf.image_convexHull hs₀
  have hTQ : T.space ⊆ Q.target := by
    rw [hf.embeddedImage_space hAi, hK₀s]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hA hx]
    exact Q.map_source (hmap hx)
  obtain ⟨J, hJ, hcv, hTJ, hJQ⟩ :=
    (T.isCompact_space_of_finite hT).exists_finite_convex_neighborhood_subset
      (hTs.symm ▸ convex_convexHull ℝ (t : Set V3)) Q.open_target hTQ
  obtain ⟨P, hP, hPs, hPc, _, _⟩ :=
    exists_finite_sphere_system_chart_carrier S sS hdis Q hQ J hJ hJQ
  have hphysical (a : Finset E) (ha : a ∈ K₀.faces) :
      Q '' ((⋃ i, S i) ∩ Q.source) ∩ convexHull ℝ (a.image A : Set V3) =
        Q '' ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))) := by
    have has : convexHull ℝ (a : Set E) ⊆ convexHull ℝ (s : Set E) := convexHull_mono ha.2
    rw [Finset.coe_image, ← hf.image_convexHull ha]
    ext x
    constructor
    · rintro ⟨⟨y, ⟨hyS, hyQ⟩, hyx⟩, u, hu, hux⟩
      have huy : g u = y := Q.injOn (hmap (has hu)) hyQ
        ((hA (has hu)).trans (hux.trans hyx.symm))
      exact ⟨y, ⟨hyS, u, hu, huy⟩, hyx⟩
    · rintro ⟨y, ⟨hyS, u, hu, huy⟩, hyx⟩
      exact ⟨⟨y, ⟨hyS, huy ▸ hmap (has hu)⟩, hyx⟩,
        u, hu, (hA (has hu)).symm.trans (by change Q (g u) = x; rw [huy, hyx])⟩
  have hPv : Disjoint P.space T.vertices := by
    apply disjoint_left.mpr
    intro x hxP hxT
    rw [hf.embeddedImage_vertices hAi] at hxT
    obtain ⟨v, hv, rfl⟩ := hxT
    have hvK : v ∈ K.vertices := hv.1
    have hvhull : v ∈ convexHull ℝ (s : Set E) :=
      hK₀s.subset (K₀.vertices_subset_space hv)
    obtain ⟨y, ⟨hyS, hyQ⟩, hyA⟩ := (hPs.subset hxP).1
    have hygv : y = g v := Q.injOn hyQ (hmap hvhull)
      (hyA.trans (hA hvhull).symm)
    exact disjoint_left.mp hSV (hygv ▸ hyS) (mem_image_of_mem g hvK)
  have hPedge (a : Finset V3) (ha : a ∈ T.faces) (ha2 : a.card = 2) :
      (P.space ∩ convexHull ℝ (a : Set V3)).Finite := by
    rw [hf.embeddedImage_faces hAi] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb2 : b.card = 2 := by
      rwa [Finset.card_image_iff.mpr (hAi.mono (K₀.subset_space hb))] at ha2
    apply ((hedges b hb.1 hb.2 hb2).image Q).subset
    intro x hx
    exact (hphysical b hb).subset ⟨(hPs.subset hx.1).1, hx.2⟩
  let B : Set V3 := ⋃ a ∈ T.faces, ⋃ (_ : a.card = 2), convexHull ℝ (a : Set V3)
  have hBc : IsClosed B := by
    apply hT.isClosed_biUnion
    intro a _
    exact isClosed_iUnion_of_finite (fun _ => (a.finite_toSet.isCompact_convexHull ℝ).isClosed)
  let Z := B ∪ frontier J.space
  refine ⟨t, T, J, P, Z, rfl, ht3, hT, ht, hTs, hJ, hcv, hTJ, hJQ,
    hP, hPs, hPc, hPv, hPedge, rfl, hBc.union isClosed_frontier, subset_union_right, ?_⟩
  rintro x ⟨⟨hxP, hxZ⟩, hxt⟩
  have hxB : x ∈ B := hxZ.resolve_right (fun hxfront => hxfront.2 (hTJ (hTs.symm.subset hxt)))
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxB
  obtain ⟨ha2, hxa⟩ := mem_iUnion.mp hxa
  rw [hf.embeddedImage_faces hAi] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hb2 : b.card = 2 := by
    rwa [Finset.card_image_iff.mpr (hAi.mono (K₀.subset_space hb))] at ha2
  obtain ⟨y, hy, hyx⟩ := (hphysical b hb).subset ⟨(hPs.subset hxP).1, hxa⟩
  obtain ⟨U, L, hU, hyU, hL, hcover⟩ := sphere_system_subedge_contact_line_cover
    S sS hdis hs hs3 hb.2 hb2 (fun i => hcofaces i b hb.1 hb.2 hb2) hgi hSV Q hQ A hmap hA hy
  refine ⟨U, hU, hyx ▸ hyU, L, hL, ?_⟩
  rintro z ⟨⟨hzP, hzt⟩, hzU⟩
  apply hcover z ⟨⟨(hPs.subset hzP).1, ?_⟩, hzU⟩
  simpa only [t, Finset.coe_image] using hzt

end PoincareConjecture.M76
