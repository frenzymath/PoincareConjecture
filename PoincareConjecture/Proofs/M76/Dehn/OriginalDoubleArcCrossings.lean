import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgery
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSignPerturbation
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedSignedPolygonZeros
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTwoSideHeightBand
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
private theorem exists_positive_face_vertex
    (s : Finset E) (A : E →ᵃ[ℝ] ℝ) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hA : 0 < A x) :
    ∃ v ∈ s, 0 < A v := by
  by_contra h
  push Not at h
  have hbound : convexHull ℝ (s : Set E) ⊆ {y | A y ≤ 0} :=
    convexHull_min (fun v hv => h v hv) ((convex_Iic (0 : ℝ)).affine_preimage A)
  exact hA.not_ge (hbound hx)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem positive_image_preconnected
    (K : SimplicialComplex ℝ E) [DecidableEq E]
    {f : E → F} (hf : K.AffineOnFaces f)
    (B : F →ᵃ[ℝ] ℝ)
    (hG : (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | 0 < B (f (v : E))}).Preconnected) :
    IsPreconnected ((f '' K.space) ∩ {y | 0 < B y}) := by
  classical
  let V := {v : K.vertices // 0 < B (f (v : E))}
  let G := K.vertexAbstractComplex.edgeGraph.induce
    {v : K.vertices | 0 < B (f (v : E))}
  let S := (f '' K.space) ∩ {y | 0 < B y}
  have hconv : Convex ℝ {y | 0 < B y} := (convex_Ioi (0 : ℝ)).affine_preimage B
  have hface {s : Finset E} (hs : s ∈ K.faces) :
      convexHull ℝ (f '' (s : Set E)) ⊆ f '' K.space := by
    rw [← hf.image_convexHull hs]
    exact image_mono (K.convexHull_subset_space hs)
  have hedge (u v : V) (h : G.Adj u v) : JoinedIn S (f u.val) (f v.val) := by
    have he : ({(u.val : E), (v.val : E)} : Finset E) ∈ K.faces := by
      have h' := h.2
      change ({u.val, v.val} : Finset K.vertices).map
        (Function.Embedding.subtype _) ∈ K.faces at h'
      simpa only [Finset.map_insert, Finset.map_singleton,
        Function.Embedding.coe_subtype] using h'
    apply JoinedIn.of_segment_subset
    intro y hy
    refine ⟨hface he ?_, hconv.segment_subset u.property v.property hy⟩
    simpa only [Finset.coe_insert, Finset.coe_singleton, image_pair,
      convexHull_pair] using hy
  have hwalk (u v : V) (p : G.Walk u v) : JoinedIn S (f u.val) (f v.val) := by
    induction p with
    | @nil u =>
      exact JoinedIn.refl
        (show f u.val ∈ S from
          ⟨mem_image_of_mem f (K.vertices_subset_space u.val.property), u.property⟩)
    | @cons u v w h p ih => exact (hedge u v h).trans ih
  have hanchor (y : F) (hy : y ∈ S) :
      ∃ v : V, JoinedIn S (f v.val) y := by
    obtain ⟨x, hx, rfl⟩ := hy.1
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := hf s hs
    have hAx : 0 < (B.comp a.toAffineMap) x := by
      change 0 < B (a x)
      rw [← ha hxs]
      exact hy.2
    obtain ⟨v, hv, hvB⟩ := exists_positive_face_vertex s (B.comp a.toAffineMap) hxs hAx
    have hvf : 0 < B (f v) := by
      rw [ha (subset_convexHull ℝ _ hv)]
      exact hvB
    have hvK : v ∈ K.vertices := K.face_subset_vertices hs hv
    refine ⟨⟨⟨v, hvK⟩, hvf⟩, JoinedIn.of_segment_subset ?_⟩
    intro y hyseg
    refine ⟨hface hs ((convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (mem_image_of_mem f hv))
      (hf.mapsTo_convexHull hs Subset.rfl hxs) hyseg),
      hconv.segment_subset hvf hy.2 hyseg⟩
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨u, hux⟩ := hanchor x hx
    have hpath : IsPathConnected S := by
      refine ⟨x, hx, ?_⟩
      intro y hy
      obtain ⟨v, hvy⟩ := hanchor y hy
      obtain ⟨p⟩ := hG u v
      exact hux.symm.trans ((hwalk u v p).trans hvy)
    exact hpath.isConnected.isPreconnected
  · change IsPreconnected S
    rw [not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem repaired_zero_positive_approach
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F} (hf : K.AffineOnFaces f) (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ)
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B (f v))
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B (f v) < 0)
    (hacc : ∀ x ∈ K.space, A x = 0 → x ∈ closure (K.space ∩ {y | 0 < A y}))
    {x : E} (hx : x ∈ K.space) (hxB : B (f x) = 0) :
    f x ∈ closure ((f '' K.space) ∩ {y | 0 < B y}) := by
  classical
  have hzero (v : E) (hv : v ∈ K.vertices) (hvB : B (f v) = 0) : A v = 0 := by
    rcases lt_trichotomy (A v) 0 with hn | hz | hp
    · exact ((hneg v hv hn).ne hvB).elim
    · exact hz
    · exact ((hpos v hv hp).ne' hvB).elim
  have hpositive : ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set E) ∧
      ∃ v ∈ s, 0 < B (f v) := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    by_cases hp : ∃ v ∈ s, 0 < B (f v)
    · exact ⟨s, hs, hxs, hp⟩
    have hnonpos (v : E) (hv : v ∈ s) : B (f v) ≤ 0 :=
      le_of_not_gt (fun h => hp ⟨v, hv, h⟩)
    obtain ⟨a, ha⟩ := hf s hs
    let C : E →ᵃ[ℝ] ℝ := (-B).comp a.toAffineMap
    have hC (v : E) (hv : v ∈ s) : 0 ≤ C v := by
      change 0 ≤ -B (a v)
      rw [← ha (subset_convexHull ℝ _ hv)]
      exact neg_nonneg.mpr (hnonpos v hv)
    have hxC : C x = 0 := by
      change -B (a x) = 0
      rw [← ha hxs, hxB, neg_zero]
    have hxs0 := s.mem_convexHull_zero_vertices C hC hxs hxC
    have hxA : A x = 0 := by
      have hverts : (s : Set E) ∩ {v | C v = 0} ⊆ {v | A v = 0} := by
        intro v hv
        apply hzero v (K.face_subset_vertices hs hv.1)
        have hvB : B (a v) = 0 := neg_eq_zero.mp hv.2
        rwa [← ha (subset_convexHull ℝ _ hv.1)] at hvB
      exact convexHull_min hverts ((convex_singleton (0 : ℝ)).affine_preimage A) hxs0
    let T : Set (Finset E) := {t | t ∈ K.faces ∧ ∃ v ∈ t, 0 < A v}
    let U : Set E := ⋃ t ∈ T, convexHull ℝ (t : Set E)
    have hT : T.Finite := hK.subset (fun _ ht => ht.1)
    have hU : IsClosed U := hT.isClosed_biUnion
      (fun t _ => t.finite_toSet.isCompact_convexHull ℝ |>.isClosed)
    have hcover : K.space ∩ {y | 0 < A y} ⊆ U := by
      intro y hy
      obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy.1
      exact mem_iUnion₂.mpr
        ⟨t, ⟨ht, exists_positive_face_vertex t A hyt hy.2⟩, hyt⟩
    have hxU := closure_minimal hcover hU (hacc x hx hxA)
    obtain ⟨t, ⟨ht, v, hv, hvA⟩, hxt⟩ := mem_iUnion₂.mp hxU
    exact ⟨t, ht, hxt, v, hv, hpos v (K.face_subset_vertices ht hv) hvA⟩
  obtain ⟨s, hs, hxs, v, hv, hvB⟩ := hpositive
  have hface : convexHull ℝ (f '' (s : Set E)) ⊆ f '' K.space := by
    rw [← hf.image_convexHull hs]
    exact image_mono (K.convexHull_subset_space hs)
  have hlimit := (convex_convexHull ℝ (f '' (s : Set E))).mem_closure_upper_affine_height
    B (hf.mapsTo_convexHull hs Subset.rfl hxs)
    (subset_convexHull ℝ _ (mem_image_of_mem f hv)) (by simpa only [hxB] using hvB)
  have h := closure_mono (inter_subset_inter_left _ hface) hlimit
  simpa only [hxB] using h

theorem exists_repaired_crossed_link_bands
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPK : P.boundary ℝ = K.space)
    {f : E → F} (hf : K.AffineOnFaces f) (hfi : InjOn f K.space)
    (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ)
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B (f v))
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B (f v) < 0)
    (hzero : (K.space ∩ {x | A x = 0}).ncard = 2)
    (hnegn : ∃ x ∈ K.space, A x < 0) (hposn : ∃ x ∈ K.space, 0 < A x) :
    ∃ (m : ℕ) (Q : Polygon F (m + 3)) (a b : F),
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧ Q.boundary ℝ = f '' K.space ∧
      a ≠ b ∧ (Q.boundary ℝ ∩ {y | B y = 0}) = {a, b} ∧
      IsFinitePLBallPair ℝ (Q.boundary ℝ ∩ {y | B y ≤ 0}) {a, b} ∧
      IsFinitePLBallPair ℝ (Q.boundary ℝ ∩ {y | 0 ≤ B y}) {a, b} ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ ∃ l r : Set F,
        Disjoint l r ∧ Q.boundary ℝ ∩ {y | B y ∈ Icc (-δ) δ} = l ∪ r ∧
        ∃ d₀ : Icc (-δ) δ ≃ₜ l, ∃ d₁ : Icc (-δ) δ ≃ₜ r,
          d₀.IsFinitePL ∧ d₁.IsFinitePL ∧
          (∀ t, B (d₀ t) = (t : ℝ)) ∧ (∀ t, B (d₁ t) = (t : ℝ)) ∧
          (∀ hz : (0 : ℝ) ∈ Icc (-δ) δ, (d₀ ⟨0, hz⟩ : F) = a) ∧
          (∀ hz : (0 : ℝ) ∈ Icc (-δ) δ, (d₁ ⟨0, hz⟩ : F) = b) := by
  classical
  obtain ⟨hnold, hpold, hzold⟩ := P.strict_sign_data hP hPi A
    A.continuous_of_finiteDimensional.continuousOn
    (by simpa only [hPK] using hzero)
    (by simpa only [hPK] using hnegn) (by simpa only [hPK] using hposn)
  rw [hPK] at hnold hpold hzold
  have hpgraph := K.preconnected_positive_vertex_graph_of_sign_preservation
    hK A (fun x => B (f x)) hpold.isPreconnected hpos hneg
      (fun v hv hz => (hzold v (K.vertices_subset_space hv) hz).2)
  have hnverts (v : E) (hv : v ∈ K.vertices) (h : 0 < (-A) v) :
      0 < (-B) (f v) := neg_pos.mpr (hneg v hv (neg_pos.mp h))
  have hpverts (v : E) (hv : v ∈ K.vertices) (h : (-A) v < 0) :
      (-B) (f v) < 0 := neg_neg_of_pos (hpos v hv (neg_lt_zero.mp h))
  have hnacc : ∀ x ∈ K.space, (-A) x = 0 →
      x ∈ closure (K.space ∩ {y | 0 < (-A) y}) := by
    intro x hx h
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      (hzold x hx (neg_eq_zero.mp h)).1
  have hngraph := K.preconnected_positive_vertex_graph_of_sign_preservation
    hK (-A) (fun x => (-B) (f x))
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hnold.isPreconnected)
      hnverts hpverts (fun v hv hz => hnacc v (K.vertices_subset_space hv) hz)
  have hpnew := positive_image_preconnected K hf B hpgraph
  have hnnew : IsPreconnected ((f '' K.space) ∩ {y | B y < 0}) := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      positive_image_preconnected K hf (-B) hngraph
  have hznew : ∀ y ∈ f '' K.space, B y = 0 →
      y ∈ closure ((f '' K.space) ∩ {z | B z < 0}) ∧
        y ∈ closure ((f '' K.space) ∩ {z | 0 < B z}) := by
    rintro _ ⟨x, hx, rfl⟩ hxB
    refine ⟨?_, repaired_zero_positive_approach K hK hf A B hpos hneg
      (fun z hz h => (hzold z hz h).2) hx hxB⟩
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      repaired_zero_positive_approach K hK hf (-A) (-B) hnverts hpverts hnacc hx
        (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hxB)
  have hnewpos (C : E →ᵃ[ℝ] ℝ) (D : F →ᵃ[ℝ] ℝ)
      (hCD : ∀ v ∈ K.vertices, 0 < C v → 0 < D (f v))
      (hne : ∃ x ∈ K.space, 0 < C x) : ∃ y ∈ f '' K.space, 0 < D y := by
    obtain ⟨x, hx, hCx⟩ := hne
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨v, hv, hvC⟩ := exists_positive_face_vertex s C hxs hCx
    have hvK := K.face_subset_vertices hs hv
    exact ⟨f v, mem_image_of_mem f (K.vertices_subset_space hvK), hCD v hvK hvC⟩
  have hpnewn := hnewpos A B hpos hposn
  have hnnewn : ∃ y ∈ f '' K.space, B y < 0 := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      hnewpos (-A) (-B) hnverts
        (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hnegn)
  obtain ⟨m, Q, hQi, hQ, hQimage⟩ := P.exists_polygon_finitePL_image hP hPi
    (hf.finitePiecewiseAffineOn hK) hPK.subset (hfi.mono hPK.subset)
  have hQK : Q.boundary ℝ = f '' K.space := by simpa only [hPK] using hQimage
  have hzQ : (Q.boundary ℝ ∩ {y | B y = 0}).ncard = 2 := by
    apply Q.ncard_zero_eq_two_of_preconnected_signs hQ hQi B
      B.continuous_of_finiteDimensional.continuousOn
    · simpa only [hQK] using hnnew
    · simpa only [hQK] using hpnew
    · simpa only [hQK] using hznew
    · simpa only [hQK] using hnnewn
    · simpa only [hQK] using hpnewn
  obtain ⟨a, b, hab, hzeros⟩ := ncard_eq_two.mp hzQ
  obtain ⟨hminus, hplus⟩ := Q.isFinitePLBallPair_signed_halves hQ hQi B
    B.continuous_of_finiteDimensional.continuousOn hab hzeros
    (by simpa only [hQK] using hnnewn) (by simpa only [hQK] using hpnewn)
  refine ⟨m, Q, a, b, hQi, hQ, hQK, hab, hzeros, hminus, hplus, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε, l, r, hdisj, hband, d₀, d₁, hd₀, hd₁, h₀, h₁, hzero₀, hzero₁⟩ :=
    Q.exists_two_side_height_band hQ hQi B hab hzeros
      (fun y hy hz => by
        have h := hznew y (hQK.subset hy) hz
        simpa only [hQK] using And.intro h.2 h.1) hε
  exact ⟨δ, hδ, hδε, l, r, hdisj, hband, d₀, d₁, hd₀, hd₁, h₀, h₁, hzero₀, hzero₁⟩

end PoincareConjecture.M76.Dehn
