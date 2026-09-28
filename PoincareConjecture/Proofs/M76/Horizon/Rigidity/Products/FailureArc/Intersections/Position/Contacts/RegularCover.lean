import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.ProtectedCover
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.IntervalGerms
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalTriangleMixedSigns











set_option autoImplicit false

open Set Geometry Module Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem original_subedge_two_segment_germs
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (hAtlas : ∀ y ∈ S, ∃ i, y ∈ (e i).source) (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (has : a ⊆ s) (ha2 : a.card = 2)
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {y : X} (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
          intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))) ∩ U,
        ∃ u v : V3, u ≠ x ∧ v ≠ x ∧ segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ z in 𝓝 x,
            z ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E)) ↔
              z ∈ segment ℝ x u ∪ segment ℝ x v := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp ha2
  obtain ⟨w, hw, rfl⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨has, by rw [Finset.card_pair hpq, hs3]⟩
  have hwp : w ≠ p := fun he => hw (he.symm ▸ Finset.mem_insert_self _ _)
  have hwq : w ≠ q := fun he => hw (he.symm ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))
  simp only [Finset.coe_insert, Finset.coe_singleton] at hmap hA ⊢
  have hy' : y ∈ S ∩ (g '' segment ℝ p q) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hy
  exact h.exists_surface_interior_two_segment_germs_of_affine_chart
    hAtlas hgi hSV hpq hwp hwq hs hy' Q hQ A hmap hA




theorem exists_original_planar_triangle_regular_cover
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (Source : SimplicialComplex ℝ (ℝ × ℝ)) (hSource : Source.faces.Finite)
    {f : (ℝ × ℝ) → X} (hf₀ : PolyhedralPLInCharts e f Source.space)
    (hfS : f '' Source.space = S) (K : SimplicialComplex ℝ E) (g : E → X)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      (S ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      HasOriginalEdgeCofaceCharts e S K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ (t : Finset V3) (T J P : SimplicialComplex ℝ V3) (Z Ω : Set V3)
      (L : V3 →ᵃ[ℝ] ℝ),
      t = s.image A ∧ t.card = 3 ∧ T.faces.Finite ∧ t ∈ T.faces ∧
      T.space = convexHull ℝ (t : Set V3) ∧
      J.faces.Finite ∧ Convex ℝ J.space ∧ T.space ⊆ interior J.space ∧
      J.space ⊆ Q.target ∧ P.faces.Finite ∧
      P.space = Q '' (S ∩ Q.source) ∩ J.space ∧
      (∀ a ∈ P.faces, a.card ≤ 3) ∧ Disjoint P.space T.vertices ∧
      (∀ a ∈ T.faces, a.card = 2 → (P.space ∩ convexHull ℝ (a : Set V3)).Finite) ∧
      Z = (⋃ a ∈ T.faces, ⋃ (_ : a.card = 2), convexHull ℝ (a : Set V3)) ∪
        frontier J.space ∧ IsClosed Z ∧ frontier J.space ⊆ Z ∧
      (∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set V3),
        ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
          ∃ B : Finset (AffineSubspace ℝ V3),
            (∀ H ∈ B, finrank ℝ H.direction ≤ 1) ∧
            ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ H ∈ B, y ∈ H) ∧
      L.linear ≠ 0 ∧ (∀ x, L x = 0 ↔ x ∈ affineSpan ℝ (t : Set V3)) ∧
      IsOpen Ω ∧ Ω ⊆ interior J.space ∧ P.space ∩ Z ∩ convexHull ℝ (t : Set V3) ⊆ Ω ∧
      ∀ x ∈ (P.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) ∩ Ω,
        (∃ u v : V3, u ≠ x ∧ v ≠ x ∧ segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ z in 𝓝 x, z ∈ P.space ∩ {z | L z = 0} ↔
            z ∈ segment ℝ x u ∪ segment ℝ x v) ∧
        x ∈ closure (P.space ∩ {z | L z < 0}) ∧
        x ∈ closure (P.space ∩ {z | 0 < L z}) := by
  classical
  have hAtlas : ∀ y ∈ S, ∃ i, y ∈ (e i).source := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hfS.symm.subset hy
    obtain ⟨i, P, V, _, _, _, hxV, hVP, hPe, _⟩ := hf₀.coordinates ⟨x, hx⟩
    exact ⟨i, hPe (hVP (mem_image_of_mem Subtype.val hxV))⟩
  obtain ⟨t, T, J, P, Z, htimage, ht3, hT, ht, hTs, hJ, hcv, hTJ, hJQ,
      hP, hPs, hPc, hPv, hPe, hZeq, hZ, hfront, hcover⟩ :=
    exists_original_planar_triangle_protected_cover Source hSource hf₀ hfS K g hgi hSV hs hs3 hedges
      hcofaces Q hQ A hmap hA
  have hdimt : finrank ℝ (affineSpan ℝ (t : Set V3)).direction = 2 := by
    rw [direction_affineSpan]
    have hrange : range ((↑) : t → V3) = (t : Set V3) := by ext x; simp
    have hh := (T.indep ht).finrank_vectorSpan (n := 2) (by simpa using ht3)
    rw [hrange] at hh
    exact hh
  obtain ⟨L, hL, hLplane⟩ :=
    (affineSpan ℝ (t : Set V3)).exists_defining_height_of_finrank_two
      (by simp) hdimt ((T.nonempty_of_mem_faces ht).to_set.mono (subset_affineSpan ℝ _))
  have hLimage : ∀ x, L x = 0 ↔ x ∈ affineSpan ℝ (A '' (s : Set E)) := by
    simpa only [htimage, Finset.coe_image] using hLplane
  have hhull : convexHull ℝ (t : Set V3) = convexHull ℝ (A '' (s : Set E)) := by
    rw [htimage, Finset.coe_image]
  let Good (x : V3) : Prop :=
    (∃ u v : V3, u ≠ x ∧ v ≠ x ∧ segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
      ∀ᶠ z in 𝓝 x, z ∈ P.space ∩ {z | L z = 0} ↔
        z ∈ segment ℝ x u ∪ segment ℝ x v) ∧
      x ∈ closure (P.space ∩ {z | L z < 0}) ∧ x ∈ closure (P.space ∩ {z | 0 < L z})
  have hregular (a : Finset E) (ha : a ∈ K.faces) (has : a ⊆ s) (ha2 : a.card = 2)
      (y : X) (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E))) :
      ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ interior J.space ∧
        ∀ x ∈ (P.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) ∩ U,
          Good x := by
    obtain ⟨Ug, hUg, hyUg, _, hgerm⟩ := original_subedge_two_segment_germs
      hAtlas hs hs3 has ha2 (hcofaces a ha has ha2) hgi hSV Q hQ A hmap hA hy
    obtain ⟨Us, hUs, hyUs, _, hsigns⟩ :=
      (hcofaces a ha has ha2).exists_triangle_mixed_signs_in_chart hs hs3 has ha2
        hgi hSV hy Q A hmap hA L hL hLimage
    have hyJ : Q y ∈ interior J.space := by
      obtain ⟨z, hz, hzy⟩ := hy.2
      have hzS := convexHull_mono has hz
      have hzA : A z ∈ convexHull ℝ (t : Set V3) := by
        rw [hhull]
        exact (A.toAffineMap.image_convexHull (s : Set E)).subset ⟨z, hzS, rfl⟩
      have hyA : Q y = A z := (congrArg Q hzy).symm.trans (hA hzS)
      rw [hyA]
      exact hTJ (hTs.symm.subset hzA)
    refine ⟨Ug ∩ Us ∩ interior J.space, (hUg.inter hUs).inter isOpen_interior,
      ⟨⟨hyUg, hyUs⟩, hyJ⟩, inter_subset_right, ?_⟩
    intro x hx
    have hxQ : x ∈ Q '' (S ∩ Q.source) := (hPs.subset hx.1.1).1
    have hxi : x ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) :=
      hhull ▸ hx.1.2
    obtain ⟨u, v, hu, hv, hinter, hg⟩ := hgerm x ⟨⟨hxQ, hxi⟩, hx.2.1.1⟩
    have hsg := hsigns x ⟨⟨hxQ, hxi⟩, hx.2.1.2⟩
    have hplane := eventually_mem_iff_mem_affineSpan_of_intrinsicInterior hx.1.2
    simp only [affineSpan_convexHull] at hplane
    refine ⟨⟨u, v, hu, hv, hinter, ?_⟩, ?_, ?_⟩
    · filter_upwards [hg, hplane, isOpen_interior.mem_nhds hx.2.2] with z hzg hzp hzJ
      have heq : z ∈ P.space ∩ {z | L z = 0} ↔
          z ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (t : Set V3) := by
        constructor
        · rintro ⟨hzP, hzL⟩
          exact ⟨(hPs.subset hzP).1, hzp.mpr ((hLplane z).mp hzL)⟩
        · rintro ⟨hzQ, hzt⟩
          exact ⟨hPs.symm.subset ⟨hzQ, interior_subset hzJ⟩,
            (hLplane z).mpr (hzp.mp hzt)⟩
      exact heq.trans (by simpa only [hhull] using hzg)
    · apply closure_mono (s := (Q '' (S ∩ Q.source) ∩ {z | L z < 0}) ∩ interior J.space)
        (t := P.space ∩ {z | L z < 0})
        (fun z hz => ⟨hPs.symm.subset ⟨hz.1.1, interior_subset hz.2⟩, hz.1.2⟩)
      exact isOpen_interior.closure_inter ⟨hsg.1, hx.2.2⟩
    · apply closure_mono (s := (Q '' (S ∩ Q.source) ∩ {z | 0 < L z}) ∩ interior J.space)
        (t := P.space ∩ {z | 0 < L z})
        (fun z hz => ⟨hPs.symm.subset ⟨hz.1.1, interior_subset hz.2⟩, hz.1.2⟩)
      exact isOpen_interior.closure_inter ⟨hsg.2, hx.2.2⟩
  let Valid (U : Set V3) : Prop := IsOpen U ∧ U ⊆ interior J.space ∧
    ∀ x ∈ (P.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) ∩ U, Good x
  let Ω : Set V3 := ⋃ (U : Set V3) (_ : Valid U), U
  have hΩ : IsOpen Ω := isOpen_iUnion fun U => isOpen_iUnion fun h => h.1
  have hΩJ : Ω ⊆ interior J.space := by
    intro x hx
    obtain ⟨U, hU, hxU⟩ := mem_iUnion₂.mp hx
    exact hU.2.1 hxU
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hcontact : P.space ∩ Z ∩ convexHull ℝ (t : Set V3) ⊆ Ω := by
    rintro x ⟨⟨hxP, hxZ⟩, hxt⟩
    rw [hZeq] at hxZ
    have hxedges := hxZ.resolve_right
      (fun hxfront => hxfront.2 (hTJ (hTs.symm.subset hxt)))
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxedges
    obtain ⟨ha2, hxa⟩ := mem_iUnion.mp hxa
    obtain ⟨z, hza⟩ := ((T.nonempty_of_mem_faces ha).to_set.convexHull).intrinsicInterior
      (convex_convexHull ℝ _)
    have hat : a ⊆ t := T.subset_of_mem_intrinsicInterior_face ha ht hza
      (hTs.subset (T.convexHull_subset_space ha (intrinsicInterior_subset hza)))
    rw [htimage] at hat
    obtain ⟨b, hbs, hba⟩ := Finset.subset_image_iff.mp hat
    have hbi : InjOn A (b : Set E) :=
      hAi.mono ((subset_convexHull ℝ (b : Set E)).trans (convexHull_mono hbs))
    have hb2 : b.card = 2 := by
      rw [← hba, Finset.card_image_iff.mpr hbi] at ha2
      exact ha2
    have hb : b ∈ K.faces := K.down_closed hs hbs (Finset.card_pos.mp (by omega))
    have hxAb : x ∈ A '' convexHull ℝ (b : Set E) := by
      rw [← hba, Finset.coe_image] at hxa
      exact (A.toAffineMap.image_convexHull (b : Set E)).symm.subset hxa
    obtain ⟨v, hv, hvx⟩ := hxAb
    obtain ⟨y, ⟨hyS, hyQ⟩, hyx⟩ := (hPs.subset hxP).1
    have hgv : g v = y := Q.injOn (hmap (convexHull_mono hbs hv)) hyQ
      ((hA (convexHull_mono hbs hv)).trans (hvx.trans hyx.symm))
    obtain ⟨U, hU, hyU, hUJ, hgood⟩ := hregular b hb hbs hb2 y ⟨hyS, v, hv, hgv⟩
    exact mem_iUnion₂.mpr ⟨U, ⟨hU, hUJ, hgood⟩, hyx ▸ hyU⟩
  refine ⟨t, T, J, P, Z, Ω, L, htimage, ht3, hT, ht, hTs, hJ, hcv, hTJ, hJQ,
    hP, hPs, hPc, hPv, hPe, hZeq, hZ, hfront, hcover, hL, hLplane,
    hΩ, hΩJ, hcontact, ?_⟩
  intro x hx
  obtain ⟨U, hU, hxU⟩ := mem_iUnion₂.mp hx.2
  exact hU.2.2 x ⟨hx.1, hxU⟩

end PoincareConjecture.M76

