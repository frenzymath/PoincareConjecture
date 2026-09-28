import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereEdgeIncidence
import PoincareConjecture.Proofs.M76.Mathlib.RegularSlicePolygons
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection
import PoincareConjecture.Proofs.M76.Mathlib.AffineInnermostDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleNormalCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

private theorem edge_zero_intrinsicInterior
    (P : SimplicialComplex ℝ V3) (hP : P.faces.Finite)
    (A : V3 →ᵃ[ℝ] ℝ) (hreg : ∀ v ∈ P.vertices, A v ≠ 0)
    {s : Finset V3} (hs : s ∈ P.faces) (hs2 : s.card = 2)
    {x : V3} (hx : x ∈ convexHull ℝ (s : Set V3)) (hAx : A x = 0) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)) := by
  obtain ⟨t,ht,hxt⟩ := P.exists_face_intrinsicInterior_of_finite hP
    (P.convexHull_subset_space hs hx)
  have hts := P.subset_of_mem_intrinsicInterior_face ht hs hxt hx
  have htpos := Finset.card_pos.mpr (P.nonempty_of_mem_faces ht)
  have htbound := Finset.card_le_card hts
  have htne : t.card ≠ 1 := by
    intro ht1
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp ht1
    have hxv : x = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        intrinsicInterior_subset hxt
    exact hreg v ht (hxv ▸ hAx)
  have hteq : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
  exact hteq ▸ hxt

private theorem regular_section_of_crossing_cofaces
    (P : SimplicialComplex ℝ V3) (hP : P.faces.Finite)
    (A : V3 →ᵃ[ℝ] ℝ) (hreg : ∀ v ∈ P.vertices, A v ≠ 0)
    (hbound : ∀ s ∈ P.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ P.faces,
      s.IsBichromaticPair (fun v => decide (0 < A v)) →
      {t : Finset V3 | t ∈ P.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) :
    HasDisjointPolygonPresentation (P.space ∩ {x | A x = 0}) := by
  classical
  let : Finite (P.regularCrossingEdges A) := (P.finite_regularCrossingEdges A hP).to_subtype
  have hdegree (s : P.regularCrossingEdges A) :
      ((P.regularSliceGraph A).neighborSet s).ncard = 2 :=
    P.toPreAbstractSimplicialComplex.crossingEdgeGraph_two_neighbors _ hcofaces s
  obtain ⟨n,L,hL,hcover,hdis⟩ :=
    (P.regularSliceGraph A).exists_component_polygons_of_two_neighbors
      (P.regularCrossingPoint A hreg) hdegree (P.regularCrossingPoint_injective A hreg)
      (fun {_ _ _ _} hef hgk => P.regularSliceGraph_segment_inter A hreg hef hgk)
  have hcarrier : P.space ∩ {x | A x = 0} =
      {x | ∃ e f : P.regularCrossingEdges A, (P.regularSliceGraph A).Adj e f ∧
        x ∈ segment ℝ (P.regularCrossingPoint A hreg e) (P.regularCrossingPoint A hreg f)} := by
    ext x
    constructor
    · rintro ⟨hx,hAx⟩
      obtain ⟨s,hs,hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      have hspos := Finset.card_pos.mpr (P.nonempty_of_mem_faces hs)
      have hsbound := hbound s hs
      have hsne : s.card ≠ 1 := by
        intro hs1
        obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs1
        have hxv : x = v := by
          simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hxs
        exact hreg v hs (hxv ▸ hAx)
      have hex : ∃ t ∈ P.faces, t.card = 3 ∧ s ⊆ t := by
        by_cases hs3 : s.card = 3
        · exact ⟨s,hs,hs3,Finset.Subset.rfl⟩
        have hs2 : s.card = 2 := by omega
        have hregs : ∀ v ∈ s, A v ≠ 0 := fun v hv => hreg v (P.face_subset_vertices hs hv)
        have hcross := (A.straddlesZero_iff_bichromatic s hregs).mp
          (A.straddlesZero_of_regular_zero hs2 hregs hxs hAx)
        have hn : {t : Finset V3 | t ∈ P.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard ≠ 0 := by
          rw [hcofaces s hs hcross]
          norm_num
        exact Set.nonempty_of_ncard_ne_zero hn
      obtain ⟨t,ht,ht3,hst⟩ := hex
      have hxt := convexHull_mono hst hxs
      have hregt : ∀ v ∈ t, A v ≠ 0 := fun v hv => hreg v (P.face_subset_vertices ht hv)
      obtain ⟨e,f,he,hf,het,hft,hne,hslice⟩ :=
        A.exists_straddling_edges_triangle ht3 hregt ⟨x,hxt,hAx⟩
      have heP : e ∈ P.faces := P.down_closed ht het
        (Finset.card_pos.mp (by rw [AffineMap.StraddlesZero.card A he]; decide))
      have hfP : f ∈ P.faces := P.down_closed ht hft
        (Finset.card_pos.mp (by rw [AffineMap.StraddlesZero.card A hf]; decide))
      let e' : P.regularCrossingEdges A := ⟨e,heP,
        (A.straddlesZero_iff_bichromatic e (fun v hv => hregt v (het hv))).mp he⟩
      let f' : P.regularCrossingEdges A := ⟨f,hfP,
        (A.straddlesZero_iff_bichromatic f (fun v hv => hregt v (hft hv))).mp hf⟩
      refine ⟨e',f',⟨fun h => hne (congrArg Subtype.val h),t,ht,ht3,het,hft⟩,?_⟩
      change x ∈ segment ℝ (A.straddlingPoint e he) (A.straddlingPoint f hf)
      rw [← hslice]
      exact ⟨hxt,hAx⟩
    · rintro ⟨e,f,hef,hx⟩
      obtain ⟨t,ht,_,_,_,hslice⟩ := P.regularSliceGraph_segment A hreg hef
      rw [hslice] at hx
      exact ⟨P.convexHull_subset_space ht hx.1,hx.2⟩
  exact hasDisjointPolygonPresentation_of_family n L
    (fun C => ⟨(hL C).1,(hL C).2.1⟩) (hcarrier.trans hcover) hdis

theorem ChartwisePLSphere.regular_cocore_section_of_carrier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hP : P.faces.Finite) (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    (hbound : ∀ f ∈ P.faces, f.card ≤ 3)
    (A : V3 →ᵃ[ℝ] ℝ) (t : ℝ) (hregular : ∀ v ∈ P.vertices, A v ≠ t)
    (hinside : P.space ∩ {x | A x = t} ⊆ interior J.space) :
    HasDisjointPolygonPresentation (P.space ∩ {x | A x = t}) := by
  classical
  let B : V3 →ᵃ[ℝ] ℝ := A - AffineMap.const ℝ V3 t
  have hreg : ∀ v ∈ P.vertices, B v ≠ 0 :=
    fun v hv hzero => hregular v hv (sub_eq_zero.mp hzero)
  have hcofaces : ∀ f ∈ P.faces,
      f.IsBichromaticPair (fun v => decide (0 < B v)) →
      {u : Finset V3 | u ∈ P.faces ∧ u.card = 3 ∧ f ⊆ u}.ncard = 2 := by
    intro edge hedge hcross
    let edge' : P.regularCrossingEdges B := ⟨edge,hedge,hcross⟩
    let x := P.regularCrossingPoint B hreg edge'
    have hx := P.regularCrossingPoint_mem B hreg edge'
    have hedge2 := AffineMap.StraddlesZero.card B
      (P.straddlesZero_of_regularCrossingEdge B hreg edge')
    have hxint := edge_zero_intrinsicInterior P hP B hreg hedge hedge2 hx.1 hx.2
    have hxP := P.convexHull_subset_space hedge hx.1
    exact s.ncard_clipped_edge_triangle_cofaces Q hQ J P hJ hJQ hP hPs
      hedge hedge2 hxint (hinside ⟨hxP,sub_eq_zero.mp hx.2⟩)
  have hh := regular_section_of_crossing_cofaces P hP B hreg hbound hcofaces
  change HasDisjointPolygonPresentation (P.space ∩ {x | A x - t = 0}) at hh
  simpa only [sub_eq_zero] using hh

theorem ChartwisePLSphere.exists_regular_cocore_section_with_carrier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (A : V3 →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      A x ∈ Ioo a b → x ∈ interior J.space) :
    ∃ P : SimplicialComplex ℝ V3, P.faces.Finite ∧
      P.space = Q '' (S ∩ Q.source) ∩ J.space ∧
      ∃ t ∈ Ioo a b, (∀ v ∈ P.vertices, A v ≠ t) ∧
      HasDisjointPolygonPresentation ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | A x = t}) := by
  classical
  obtain ⟨P,hP,hPs,hbound,_⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
  obtain ⟨t,ht,htnot⟩ := (Ioo_infinite hab).exists_notMem_finite
    ((P.finite_vertices_of_finite_faces hP).image A)
  have hreg : ∀ v ∈ P.vertices, A v ≠ t :=
    fun v hv h => htnot ⟨v,hv,h⟩
  refine ⟨P,hP,hPs,t,ht,hreg,?_⟩
  have hh := s.regular_cocore_section_of_carrier Q hQ J P hJ hJQ hP hPs hbound A t hreg
    (fun x hx => hband x (hPs.subset hx.1) (hx.2 ▸ ht))
  simpa only [hPs] using hh

theorem ChartwisePLSphere.exists_regular_cocore_section
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (A : V3 →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      A x ∈ Ioo a b → x ∈ interior J.space) :
    ∃ t ∈ Ioo a b,
      HasDisjointPolygonPresentation ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | A x = t}) := by
  obtain ⟨_,_,_,t,ht,_,hsection⟩ :=
    s.exists_regular_cocore_section_with_carrier Q hQ J hJ hJQ A hab hband
  exact ⟨t,ht,hsection⟩

theorem exists_innermost_disk_in_convex_section_with_polygon
    {T U Z : Set V3} (h : HasDisjointPolygonPresentation ((T ∩ U) ∩ Z))
    (hU : Convex ℝ U) (hinside : (T ∩ U) ∩ Z ⊆ interior U)
    (a : (ℝ × ℝ) →ᴬ[ℝ] V3) (r : V3 →ᴬ[ℝ] (ℝ × ℝ))
    (hleft : Function.LeftInverse r a) (hright : LeftInvOn a r Z)
    (ha : MapsTo a univ Z) (hne : ((T ∩ U) ∩ Z).Nonempty) :
    ∃ (n : ℕ) (L : Polygon V3 (n + 3)) (B : Set V3),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      IsFinitePLBallPair (ℝ × ℝ) B (L.boundary ℝ) ∧
      B ⊆ interior U ∩ Z ∧ B ∩ T = L.boundary ℝ ∧
      IsCompact (((T ∩ U) ∩ Z) \ L.boundary ℝ) := by
  classical
  obtain ⟨m,n,P,hP,hcover,hdis⟩ := h
  have hbd (i : Fin m) : (P i).boundary ℝ ⊆ (T ∩ U) ∩ Z := by
    rw [hcover]
    exact fun _ hx => mem_iUnion.mpr ⟨i,hx⟩
  let Q := fun i => (P i).affineImage r.toAffineMap
  have hQ (i : Fin m) : Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges ∧
      a '' (Q i).boundary ℝ = (P i).boundary ℝ :=
    (P i).affineImage_of_leftInvOn (hP i).2 (hP i).1 r.toAffineMap a.toAffineMap
      (fun _ hx => hright (hbd i hx).2)
  have hsection : a ⁻¹' (T ∩ U) = ⋃ i, (Q i).boundary ℝ := by
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover ▸ (show a y ∈ (T ∩ U) ∩ Z from
        ⟨hy,ha (mem_univ y)⟩))
      rw [← (hQ i).2.2] at hi
      exact mem_iUnion.mpr ⟨i,hleft.injective.mem_set_image.mp hi⟩
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact (hbd i ((hQ i).2.2 ▸ mem_image_of_mem a hi)).1
  have hQdis : Pairwise fun i j : Fin m => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ) := by
    intro i j hij
    apply disjoint_left.mpr
    intro y hyi hyj
    exact disjoint_left.mp (hdis hij) ((hQ i).2.2 ▸ mem_image_of_mem a hyi)
      ((hQ j).2.2 ▸ mem_image_of_mem a hyj)
  obtain ⟨x,hx⟩ := hne
  obtain ⟨i,_⟩ := mem_iUnion.mp (hcover ▸ hx)
  let : Nonempty (Fin m) := ⟨i⟩
  obtain ⟨j,hB,hBT,_⟩ := Polygon.exists_innermost_affine_disk n Q
    (fun i => (hQ i).2.1) (fun i => (hQ i).1) hQdis a hleft.injective (T ∩ U) hsection
  rw [(hQ j).2.2] at hB hBT
  have hQinside : closure (Q j).inside ⊆ a ⁻¹' interior U := by
    apply (Q j).closure_inside_subset_convex (hQ j).2.1 (hQ j).1
      (hU.interior.affine_preimage a.toAffineMap)
    rintro _ ⟨k,rfl⟩
    exact hinside (hbd j ((hQ j).2.2 ▸ mem_image_of_mem a ((Q j).vertex_mem_boundary k)))
  refine ⟨n j,P j,a '' closure (Q j).inside,(hP j).1,(hP j).2,hB,?_,?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact ⟨hQinside hy,ha (mem_univ y)⟩
  · rw [← hBT]
    ext y
    constructor
    · rintro ⟨hyB,hyT⟩
      refine ⟨hyB,hyT,?_⟩
      obtain ⟨z,hz,rfl⟩ := hyB
      exact interior_subset (hQinside hz)
    · rintro ⟨hyB,hyT,_⟩
      exact ⟨hyB,hyT⟩
  · have heq : ((T ∩ U) ∩ Z) \ (P j).boundary ℝ =
        ⋃ i : {i : Fin m // i ≠ j}, (P i).boundary ℝ := by
      ext x
      constructor
      · rintro ⟨hx,hxj⟩
        obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover ▸ hx)
        have hij : i ≠ j := fun heq => hxj (heq ▸ hi)
        exact mem_iUnion.mpr ⟨⟨i,hij⟩,hi⟩
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact ⟨hcover.symm.subset (mem_iUnion.mpr ⟨i,hi⟩),
          fun hj => disjoint_left.mp (hdis i.property) hi hj⟩
    rw [heq]
    exact isCompact_iUnion fun i => (P i).isCompact_boundary

theorem exists_innermost_disk_in_convex_section
    {T U Z : Set V3} (h : HasDisjointPolygonPresentation ((T ∩ U) ∩ Z))
    (hU : Convex ℝ U) (hinside : (T ∩ U) ∩ Z ⊆ interior U)
    (a : (ℝ × ℝ) →ᴬ[ℝ] V3) (r : V3 →ᴬ[ℝ] (ℝ × ℝ))
    (hleft : Function.LeftInverse r a) (hright : LeftInvOn a r Z)
    (ha : MapsTo a univ Z) (hne : ((T ∩ U) ∩ Z).Nonempty) :
    ∃ B q : Set V3, IsFinitePLBallPair (ℝ × ℝ) B q ∧
      B ⊆ interior U ∩ Z ∧ B ∩ T = q := by
  obtain ⟨n,L,B,_,_,hB,hsub,hmeet,_⟩ :=
    exists_innermost_disk_in_convex_section_with_polygon h hU hinside a r hleft hright ha hne
  exact ⟨B,L.boundary ℝ,hB,hsub,hmeet⟩

theorem ChartwisePLSphere.exists_original_cocore_innermost_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S R : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hJcv : Convex ℝ J.space)
    (hJR : MapsTo Q.symm J.space (interior R))
    (H : V3 ≃ᴬ[ℝ] ((ℝ × ℝ) × ℝ)) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      (H x).2 ∈ Ioo a b → x ∈ interior J.space) :
    ∃ t ∈ Ioo a b,
      ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} = ∅) ∨
      ∃ B q : Set V3, IsFinitePLBallPair (ℝ × ℝ) B q ∧
        B ⊆ interior J.space ∩ {x | (H x).2 = t} ∧
        PolyhedralPLInCharts e Q.symm B ∧ InjOn Q.symm B ∧
        MapsTo Q.symm B (interior R) ∧
        (∀ x ∈ B, Q.symm x ∈ S ↔ x ∈ q) := by
  classical
  let A : V3 →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  obtain ⟨t,ht,hsection⟩ := s.exists_regular_cocore_section Q hQ J hJ hJQ A.toAffineMap hab hband
  change HasDisjointPolygonPresentation
    ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) at hsection
  refine ⟨t,ht,?_⟩
  by_cases hempty : (Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} = ∅
  · exact Or.inl hempty
  right
  let F : (ℝ × ℝ) →ᴬ[ℝ] V3 := H.symm.toContinuousAffineMap.comp
    ((ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (ℝ × ℝ) ((0,0),t))
  let G : V3 →ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  have hF (z : ℝ × ℝ) : F z = H.symm (z,t) := by
    change H.symm ((z,0) + ((0,0),t)) = H.symm (z,t)
    have hz : z + (0,0) = z := add_zero z
    simp only [Prod.mk_add_mk, zero_add, hz]
  have hG (x : V3) : G x = (H x).1 := rfl
  have hleft : Function.LeftInverse G F := by
    intro z
    rw [hG,hF,H.apply_symm_apply]
  have hright : LeftInvOn F G {x | (H x).2 = t} := by
    intro x hx
    rw [hF,hG,← hx]
    exact H.symm_apply_apply x
  have hplane : MapsTo F univ {x | (H x).2 = t} := by
    intro z _
    change (H (F z)).2 = t
    rw [hF,H.apply_symm_apply]
  obtain ⟨B,q,hB,hBsub,hcontact⟩ := exists_innermost_disk_in_convex_section hsection hJcv
    (fun x hx => hband x hx.1 (hx.2 ▸ ht)) F G hleft hright hplane
    (Set.nonempty_iff_ne_empty.mpr hempty)
  have hBT : B ⊆ Q.target := fun x hx => hJQ (interior_subset (hBsub hx).1)
  obtain ⟨K,_,hK,hKs,_⟩ := hB.exists_finite_carrier_and_rim_complexes
  have hPL : PolyhedralPLInCharts e Q.symm B := by
    have h := polyhedralPLInCharts_of_compatible_inverse e Q (fun x _ => hcover x) hQ K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK)
      (fun x hx => hBT (hKs.subset hx))
    change PolyhedralPLInCharts e Q.symm K.space at h
    simpa only [hKs] using h
  refine ⟨B,q,hB,hBsub,hPL,Q.symm.injOn.mono hBT,
    fun x hx => hJR (interior_subset (hBsub hx).1),?_⟩
  intro x hxB
  have hxT := hBT hxB
  have hmem : Q.symm x ∈ S ↔ x ∈ Q '' (S ∩ Q.source) := by
    constructor
    · intro hxS
      exact ⟨Q.symm x,⟨hxS,Q.map_target hxT⟩,Q.right_inv hxT⟩
    · rintro ⟨y,⟨hyS,hyQ⟩,rfl⟩
      simpa only [Q.left_inv hyQ] using hyS
  rw [hmem]
  exact ⟨fun hx => hcontact.subset ⟨hxB,hx⟩,fun hx => (hcontact.symm.subset hx).2⟩

end PoincareConjecture.M76
