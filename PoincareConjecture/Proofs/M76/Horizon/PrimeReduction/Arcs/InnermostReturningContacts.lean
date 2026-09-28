import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.ReturningRibbonSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ActualFaceComponents
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskRegions
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false
open Set Geometry

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))




theorem interval_trapped_of_returning_base_contact {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) {A B D : Set V} {u v a b q : V}
    (hboundary : P.boundary ℝ = A ∪ segment ℝ u v)
    (hA : IsFinitePLBallPair ℝ A {u, v}) (hAz : A ∩ Z = {u, v})
    (hB : IsFinitePLBallPair ℝ B {a, b})
    (hBfront : B ∩ frontier D = {a, b}) (hBD : B ⊆ D)
    (hDupper : ∀ z ∈ D, 0 ≤ z.2) (hDaxis : D ∩ Z ⊆ frontier D)
    (hclosedD : closure P.inside ⊆ D) (hAB : Disjoint A B)
    (hqB : q ∈ B) (hq0 : q.2 = 0) (hq : q.1 ∈ Ioo u.1 v.1) :
    B \ {a, b} ⊆ P.inside ∧ B ⊆ closure P.inside ∧
      a ∈ segment ℝ u v ∧ b ∈ segment ℝ u v := by
  have hu : u ∈ A ∩ Z := hAz.symm.subset (by simp)
  have hv : v ∈ A ∩ Z := hAz.symm.subset (by simp)
  have hqA : q ∉ A := fun h => disjoint_left.mp hAB h hqB
  obtain ⟨δ, hδ, hrect⟩ := P.exists_returning_base_upper_rectangle hP hi hup
    hboundary hA.isCompact.isClosed hu.2 hv.2 hq0 hq hqA
  let U := Ioo (q.1 - δ) (q.1 + δ) ×ˢ Ioo (-δ) δ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hqU : q ∈ U := by
    exact ⟨⟨by linarith, by linarith⟩,
      by rw [hq0]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
  have hqcl : q ∈ closure (B \ {a, b}) := by rw [hB.closure_sdiff]; exact hqB
  obtain ⟨z, hzU, hzB⟩ := mem_closure_iff.mp hqcl U hU hqU
  have hzpos : 0 < z.2 := lt_of_le_of_ne (hDupper z (hBD hzB.1)) (by
    intro heq
    exact hzB.2 (hBfront.subset ⟨hzB.1, hDaxis ⟨hBD hzB.1, heq.symm⟩⟩))
  have hzI : z ∈ P.inside := hrect ⟨hzU.1, hzpos, hzU.2.2⟩
  have havoid : Disjoint (frontier P.inside) (B \ {a, b}) := by
    rw [P.frontier_inside hP hi]
    apply disjoint_left.mpr
    intro x hxP hxB
    rcases hboundary ▸ hxP with hxA | hxseg
    · exact disjoint_left.mp hAB hxA hxB.1
    · exact hxB.2 (hBfront.subset ⟨hxB.1, hDaxis
        ⟨hBD hxB.1, segment_subset_returning_axis hu.2 hv.2 hxseg⟩⟩)
  have hinside : B \ {a, b} ⊆ P.inside :=
    hB.isConnected_sdiff.isPreconnected.m76_subset_of_disjoint_frontier
      (P.isOpen_inside hP hi) havoid ⟨z, hzB, hzI⟩
  have hBcl : B ⊆ closure P.inside := by
    rw [← hB.closure_sdiff]
    exact closure_mono hinside
  have hends (x : V) (hx : x ∈ ({a, b} : Set V)) : x ∈ segment ℝ u v := by
    have hxB := hB.1 hx
    have hxF := (hBfront.symm.subset hx).2
    have hxcl := hBcl hxB
    have hxnot : x ∉ P.inside := by
      intro hxi
      have hxint : x ∈ interior D :=
        interior_maximal (subset_closure.trans hclosedD) (P.isOpen_inside hP hi) hxi
      exact disjoint_left.mp disjoint_interior_frontier hxint hxF
    rw [closure_eq_self_union_frontier, P.frontier_inside hP hi] at hxcl
    rcases hboundary ▸ hxcl.resolve_left hxnot with hxA | hxseg
    · exact (disjoint_left.mp hAB hxA hxB).elim
    · exact hxseg
  exact ⟨hinside, hBcl, hends a (by simp), hends b (by simp)⟩





theorem innermost_returning_base_contacts
    {κ : Type*} (B : κ → Set V) {D : Set V}
    (hBD : ∀ k, B k ⊆ D) (hdis : Pairwise fun k l => Disjoint (B k) (B l))
    (hclass : ∀ k,
      (∃ a b, IsFinitePLBallPair ℝ (B k) {a, b} ∧ B k ∩ frontier D = {a, b}) ∨
        B k ⊆ interior D)
    (hDupper : ∀ z ∈ D, 0 ≤ z.2) (hDaxis : D ∩ Z ⊆ frontier D)
    (n : {k : κ // (B k ∩ frontier D).Nonempty ∧ B k ∩ frontier D ⊆ Z} → ℕ)
    (P : ∀ i : {k : κ // (B k ∩ frontier D).Nonempty ∧ B k ∩ frontier D ⊆ Z},
      Polygon V (n i + 3))
    (u v : {k : κ // (B k ∩ frontier D).Nonempty ∧ B k ∩ frontier D ⊆ Z} → V)
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hup : ∀ i j, 0 ≤ (P i j).2)
    (hboundary : ∀ i, (P i).boundary ℝ = B i.val ∪ segment ℝ (u i) (v i))
    (hA : ∀ i, IsFinitePLBallPair ℝ (B i.val) {u i, v i})
    (hAz : ∀ i, B i.val ∩ Z = {u i, v i})
    (hclosedD : ∀ i, closure (P i).inside ⊆ D)
    (i : {k : κ // (B k ∩ frontier D).Nonempty ∧ B k ∩ frontier D ⊆ Z})
    (huv : (u i).1 < (v i).1)
    (hinner : Disjoint (P i).inside (⋃ j, (P j).boundary ℝ)) :
    (⋃ k, B k) ∩ segment ℝ (u i) (v i) = {u i, v i} := by
  have hu : u i ∈ B i.val ∩ Z := (hAz i).symm.subset (by simp)
  have hv : v i ∈ B i.val ∩ Z := (hAz i).symm.subset (by simp)
  apply Subset.antisymm
  · rintro q ⟨hqB, hqseg⟩
    obtain ⟨k, hqk⟩ := mem_iUnion.mp hqB
    have hq0 : q.2 = 0 := segment_subset_returning_axis hu.2 hv.2 hqseg
    by_cases hki : k = i.val
    · subst k
      exact (hAz i).subset ⟨hqk, hq0⟩
    have hAB : Disjoint (B i.val) (B k) := hdis (Ne.symm hki)
    have hqneq0 : q ≠ u i := fun h => disjoint_left.mp hAB (h.symm ▸ hu.1) hqk
    have hqneq1 : q ≠ v i := fun h => disjoint_left.mp hAB (h.symm ▸ hv.1) hqk
    have hqIcc : q.1 ∈ Icc (u i).1 (v i).1 := by
      rw [returning_axis_segment hu.2 hv.2 huv.le] at hqseg
      exact hqseg.1
    have hqstrict : q.1 ∈ Ioo (u i).1 (v i).1 := by
      refine ⟨lt_of_le_of_ne hqIcc.1 ?_, lt_of_le_of_ne hqIcc.2 ?_⟩
      · exact fun h => hqneq0 (Prod.ext h.symm (hq0.trans hu.2.symm))
      · exact fun h => hqneq1 (Prod.ext h (hq0.trans hv.2.symm))
    rcases hclass k with ⟨a, b, hball, hfront⟩ | hint
    · obtain ⟨hinside, _, ha, hb⟩ := (P i).interval_trapped_of_returning_base_contact
        (hP i) (hi i) (hup i) (hboundary i) (hA i) (hAz i)
        hball hfront (hBD k) hDupper hDaxis (hclosedD i) hAB hqk hq0 hqstrict
      have hret : (B k ∩ frontier D).Nonempty ∧ B k ∩ frontier D ⊆ Z := by
        rw [hfront]
        refine ⟨⟨a, by simp⟩, ?_⟩
        intro z hz
        rcases hz with rfl | hz
        · exact segment_subset_returning_axis hu.2 hv.2 ha
        · have hz' : z = b := hz
          subst z
          exact segment_subset_returning_axis hu.2 hv.2 hb
      let j : {k : κ // (B k ∩ frontier D).Nonempty ∧ B k ∩ frontier D ⊆ Z} := ⟨k, hret⟩
      obtain ⟨z, hz⟩ := hball.sdiff_nonempty
      have hzP : z ∈ (P j).boundary ℝ := (hboundary j).symm.subset (Or.inl hz.1)
      exact (disjoint_left.mp hinner (hinside hz) (mem_iUnion.mpr ⟨j, hzP⟩)).elim
    · exact (disjoint_left.mp disjoint_interior_frontier (hint hqk)
        (hDaxis ⟨hBD k hqk, hq0⟩)).elim
  · intro q hq
    rcases hq with rfl | hq
    · exact ⟨mem_iUnion.mpr ⟨i.val, hu.1⟩, left_mem_segment ℝ _ _⟩
    · have hq' : q = v i := hq
      subst q
      exact ⟨mem_iUnion.mpr ⟨i.val, hv.1⟩, right_mem_segment ℝ _ _⟩

end Polygon

namespace PoincareConjecture.M76

open TriangleDiskModel

local notation "V" => (ℝ × ℝ)
local notation "Δ" => (convexHull ℝ (range rightTriangle))
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

private theorem right_intrinsicFrontier : intrinsicFrontier ℝ Δ = frontier Δ := by
  let b : AffineBasis (Fin 3) ℝ V := ⟨rightTriangle, independent_rightTriangle,
    independent_rightTriangle.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp [Module.finrank_prod])⟩
  have hi : intrinsicInterior ℝ Δ = interior Δ :=
    Subset.antisymm (fun _ hx => b.mem_interior_convexHull_of_mem_intrinsicInterior hx)
      interior_subset_intrinsicInterior
  rw [← closure_sdiff_intrinsicInterior, hi, frontier]

private theorem right_axis : Δ ∩ Z = segment ℝ (0, 0) (1, 0) := by
  rw [Polygon.returning_axis_segment rfl rfl (by norm_num : (0 : ℝ) ≤ 1)]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod, mem_Icc]
  rw [mem_right_region_iff]
  constructor
  · rintro ⟨⟨h0, _, h1⟩, hz⟩
    exact ⟨⟨h0, by simpa only [hz, add_zero] using h1⟩, hz⟩
  · rintro ⟨⟨h0, h1⟩, hz⟩
    exact ⟨⟨h0, by simpa only [hz] using (le_refl (0 : ℝ)),
      by simpa only [hz, add_zero] using h1⟩, hz⟩

private theorem right_axis_frontier : Δ ∩ Z ⊆ frontier Δ := by
  rw [right_axis, rightTriangle.frontier_convexHull_triangle independent_rightTriangle]
  intro x hx
  apply mem_iUnion.mpr
  refine ⟨(0 : Fin 3), ?_⟩
  simpa [Polygon.edgeSet, Polygon.edgeVertices, rightTriangle, affineSegment_eq_segment] using hx



theorem affine_triangle_frontier_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (F : V →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] V) (hRF : Function.LeftInverse R F)
    {T : Set E} (hface : F '' Δ = T) {x : E} (hx : x ∈ T) :
    R x ∈ frontier Δ ↔ x ∈ intrinsicFrontier ℝ T := by
  have hfront : intrinsicFrontier ℝ T = F '' frontier Δ := by
    rw [← hface]
    change intrinsicFrontier ℝ (F.toAffineMap '' Δ) = F.toAffineMap '' frontier Δ
    rw [F.toAffineMap.intrinsicFrontier_image_of_injOn _ hRF.injective.injOn,
      right_intrinsicFrontier]
  obtain ⟨z, hz, rfl⟩ := hface.symm.subset hx
  rw [hRF z, hfront]
  exact (hRF.injective.mem_set_image).symm





theorem actual_innermost_returning_base_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (t : Finset E) (ht : t.Nonempty) (hind : AffineIndependent ℝ ((↑) : t → E))
    (hsub : G.space ⊆ convexHull ℝ (t : Set E))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))).Finite)
    (hinterior : ∀ v : G.vertices, (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices, (v : E) ∉ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (F : V →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] V) (hRF : Function.LeftInverse R F)
    (hface : F '' Δ = convexHull ℝ (t : Set E)) (base : Set E)
    (hbase : F '' segment ℝ (0, 0) (1, 0) = base) :
    let I := {C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent //
      (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
      Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆ base}
    ∀ (n : I → ℕ) (P : ∀ i, Polygon V (n i + 3)) (u v : I → V),
      (∀ i, (P i).HasSimplicialEdges) → (∀ i, Function.Injective (P i)) →
      (∀ i j, 0 ≤ (P i j).2) →
      (∀ i, (P i).boundary ℝ =
        R '' i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∪
          segment ℝ (u i) (v i)) →
      (∀ i, IsFinitePLBallPair ℝ
        (R '' i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E))) {u i, v i}) →
      (∀ i, (R '' i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E))) ∩ Z =
        {u i, v i}) →
      (∀ i, closure (P i).inside ⊆ Δ) →
      ∀ i, (u i).1 < (v i).1 →
        Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) →
        (R '' G.space) ∩ segment ℝ (u i) (v i) = {u i, v i} := by
  classical
  intro I n P u v hP hi hup hboundary hA hAz hclosedD i huv hinner
  let κ := G.vertexAbstractComplex.edgeGraph.ConnectedComponent
  let C : κ → Set E := fun k => k.toSimpleGraph.segmentCarrier (fun v => (v.val : E))
  let B : κ → Set V := fun k => R '' C k
  obtain ⟨hcover, hdis, hclasses⟩ :=
    G.exists_actual_face_components hG hdim t ht hind hsub hfinite hinterior hexterior
  have hCG (k : κ) : C k ⊆ G.space :=
    fun x hx => hcover.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)
  have hFR (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) : F (R x) = x := by
    obtain ⟨z, _, rfl⟩ := hface.symm.subset hx
    rw [hRF z]
  have hRi : InjOn R G.space := by
    intro x hx y hy hxy
    have hh := congrArg F hxy
    rwa [hFR x (hsub hx), hFR y (hsub hy)] at hh
  have hRΔ (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) : R x ∈ Δ := by
    obtain ⟨z, hz, rfl⟩ := hface.symm.subset hx
    rwa [hRF z]
  have hBD (k : κ) : B k ⊆ Δ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hRΔ x (hsub (hCG k hx))
  have hBdis : Pairwise fun k l => Disjoint (B k) (B l) := by
    intro k l hkl
    apply disjoint_left.mpr
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have he := hRi (hCG k hx) (hCG l hy) (hxz.trans hyz.symm)
    exact disjoint_left.mp (hdis hkl) hx (he.symm ▸ hy)
  have hBfront (k : κ) : B k ∩ frontier Δ =
      R '' (C k ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) := by
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, (affine_triangle_frontier_coordinates F R hRF hface
        (hsub (hCG k hx))).mp hz⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hf⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (affine_triangle_frontier_coordinates F R hRF hface
        (hsub (hCG k hx))).mpr hf⟩
  have hRbase (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) : R x ∈ Z ↔ x ∈ base := by
    constructor
    · intro hz
      exact hbase.subset ⟨R x, right_axis.subset ⟨hRΔ x hx, hz⟩, hFR x hx⟩
    · intro hxbase
      obtain ⟨z, hz, rfl⟩ := hbase.symm.subset hxbase
      rw [hRF z]
      exact (right_axis.symm.subset hz).2
  have hlabels (k : κ) := G.actual_component_frontier_eq_degree_one_vertices
    hdim t ht hind hsub hfinite hinterior hexterior k
  have hret (k : κ) :
      ((B k ∩ frontier Δ).Nonempty ∧ B k ∩ frontier Δ ⊆ Z) ↔
        (∃ v : k, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ k.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆ base := by
    constructor
    · rintro ⟨⟨z, hz⟩, haxis⟩
      obtain ⟨x, hx, _⟩ := (hBfront k).subset hz
      obtain ⟨w, hw, _⟩ := (hlabels k).subset hx
      refine ⟨⟨⟨w, hw.1⟩, hw.2⟩, ?_⟩
      intro x hx
      have hxc := (hlabels k).symm.subset hx
      exact (hRbase x (hsub (hCG k hxc.1))).mp
        (haxis ((hBfront k).symm.subset ⟨x, hxc, rfl⟩))
    · rintro ⟨⟨w, hw⟩, hbaseC⟩
      have hwf := (hlabels k).symm.subset ⟨w.val, ⟨w.property, hw⟩, rfl⟩
      refine ⟨⟨R (w.val : E), (hBfront k).symm.subset ⟨w.val, hwf, rfl⟩⟩, ?_⟩
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (hBfront k).subset hz
      exact (hRbase x (hsub (hCG k hx.1))).mpr (hbaseC ((hlabels k).subset hx))
  let J := {k : κ // (B k ∩ frontier Δ).Nonempty ∧ B k ∩ frontier Δ ⊆ Z}
  let e : J ≃ I := Equiv.subtypeEquivRight hret
  have hclass (k : κ) :
      (∃ a b, IsFinitePLBallPair ℝ (B k) {a, b} ∧ B k ∩ frontier Δ = {a, b}) ∨
        B k ⊆ interior Δ := by
    rcases hclasses k with ⟨m, f, _, hball, hrim, _⟩ | ⟨m, Q, _, _, hQ, hQi⟩
    · left
      have hball' := (hrim ▸ hball).affine_image R (hRi.mono (hCG k))
      refine ⟨R ((f 0).val : E), R ((f (Fin.last (m + 1))).val : E), ?_, ?_⟩
      · simpa only [image_insert_eq, image_singleton] using hball'
      · rw [hBfront k, hrim, image_insert_eq, image_singleton]
    · right
      rintro _ ⟨x, hx, rfl⟩
      have hxi := hQi (hQ.symm.subset hx)
      by_contra hnot
      have hxf := (affine_triangle_frontier_coordinates F R hRF hface
        (hsub (hCG k hx))).mp ⟨subset_closure (hRΔ x (hsub (hCG k hx))), hnot⟩
      rw [← intrinsicClosure_sdiff_intrinsicInterior] at hxf
      exact hxf.2 hxi
  have hinner' : Disjoint (P (e (e.symm i))).inside (⋃ j : J, (P (e j)).boundary ℝ) := by
    rw [e.apply_symm_apply]
    exact hinner.mono_right (iUnion_subset fun j => subset_iUnion
      (fun k : I => (P k).boundary ℝ) (e j))
  have hresult := Polygon.innermost_returning_base_contacts B hBD hBdis hclass
    (fun z hz => ((mem_right_region_iff z).mp hz).2.1) right_axis_frontier
    (fun j : J => n (e j)) (fun j => P (e j)) (fun j => u (e j)) (fun j => v (e j))
    (fun j => hP (e j)) (fun j => hi (e j)) (fun j => hup (e j))
    (fun j => hboundary (e j)) (fun j => hA (e j)) (fun j => hAz (e j))
    (fun j => hclosedD (e j)) (e.symm i) (by simpa only [e.apply_symm_apply] using huv) hinner'
  have hBcover : (⋃ k, B k) = R '' G.space := by
    rw [hcover, image_iUnion]
  simpa only [hBcover, e.apply_symm_apply] using hresult

end PoincareConjecture.M76
