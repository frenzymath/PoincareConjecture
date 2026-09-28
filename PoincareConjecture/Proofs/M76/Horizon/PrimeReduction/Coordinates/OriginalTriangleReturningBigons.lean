import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.ReturningComponentBigons
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage









set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76




theorem exists_original_triangle_returning_bigons
    {E V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [DecidableEq V] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s a : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (has : a ⊆ s) (ha2 : a.card = 2)
    (Q : OpenPartialHomeomorph X V) (A : E →ᴬ[ℝ] V)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V) (hG : G.faces.Finite)
    (hdim : ∀ b ∈ G.faces, b.card ≤ 2)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hreturn : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
      Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
        convexHull ℝ (A '' (a : Set E))) :
    let I := {C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent //
      (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
      Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
        convexHull ℝ (A '' (a : Set E))}
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] V) (R : V →ᴬ[ℝ] (ℝ × ℝ))
      (n : I → ℕ) (e : ∀ i, Fin (n i + 2) ≃ i.val) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3)),
      let p : ∀ i, Fin (n i + 2) → ℝ × ℝ := fun i j => R ((e i j).val : V)
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (affineSpan ℝ (A '' (s : Set E))) ∧
      F '' convexHull ℝ (range rightTriangle) = convexHull ℝ (A '' (s : Set E)) ∧
      F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ (A '' (a : Set E)) ∧
      (∀ i, Function.Injective (p i)) ∧
      (∀ i (r s : Fin (n i + 1)),
        segment ℝ ((p i) r.castSucc) ((p i) r.succ) ∩
            segment ℝ ((p i) s.castSucc) ((p i) s.succ) ⊆
          convexHull ℝ (({(p i) r.castSucc, (p i) r.succ} : Set (ℝ × ℝ)) ∩
            {(p i) s.castSucc, (p i) s.succ})) ∧
      (∀ i j, 0 ≤ (p i j).2) ∧
      (∀ i, Polygon.pathCarrier (p i) ∩ {z : ℝ × ℝ | z.2 = 0} =
        {p i 0, p i (Fin.last (n i + 1))}) ∧
      Pairwise (fun i j => Disjoint (Polygon.pathCarrier (p i)) (Polygon.pathCarrier (p j))) ∧
      (∀ i, R '' i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V)) =
        Polygon.pathCarrier (p i)) ∧
      (∀ i, F '' Polygon.pathCarrier (p i) =
        i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V))) ∧
      (∀ i, IsFinitePLBallPair ℝ (i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V)))
        {((e i 0).val : V), ((e i (Fin.last (n i + 1))).val : V)}) ∧
      (∀ i, Subtype.val '' {v : G.vertices | v ∈ i.val.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} =
        {((e i 0).val : V), ((e i (Fin.last (n i + 1))).val : V)}) ∧
      (∀ i, (P i).HasSimplicialEdges ∧ Function.Injective (P i)) ∧
      (∀ i j, 0 ≤ (P i j).2) ∧
      (∀ i, (P i).boundary ℝ = Polygon.pathCarrier (p i) ∪
        segment ℝ (p i 0) (p i (Fin.last (n i + 1)))) ∧
      (∀ i, F '' (P i).boundary ℝ =
        i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V)) ∪
          segment ℝ ((e i 0).val : V) ((e i (Fin.last (n i + 1))).val : V)) ∧
      (∀ i, closure (P i).inside ⊆ convexHull ℝ (range rightTriangle)) ∧
      ∃ i, IsFinitePLBallPair (ℝ × ℝ) (closure (P i).inside) ((P i).boundary ℝ) ∧
        closure (P i).inside ∩ {z : ℝ × ℝ | z.2 = 0} =
          segment ℝ (p i 0) (p i (Fin.last (n i + 1))) ∧
        closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
        Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := by
  classical
  let K₀ : SimplicialComplex ℝ E :=
    { faces := {b | b ∈ K.faces ∧ b ⊆ s}
      indep := fun hb => K.indep hb.1
      isRelLowerSet_faces := by
        intro b hb
        exact ⟨K.nonempty_of_mem_faces hb.1, fun c hcb hc =>
          ⟨K.down_closed hb.1 hcb hc, hcb.trans hb.2⟩⟩
      inter_subset_convexHull := fun hb hc => K.inter_subset_convexHull hb.1 hc.1 }
  have hs₀ : s ∈ K₀.faces := ⟨hs, Finset.Subset.rfl⟩
  have hK₀s : K₀.space = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨b, hb, hxb⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact convexHull_mono hb.2 hxb
    · exact K₀.convexHull_subset_space hs₀
  have hAi : InjOn A K₀.space := by
    intro x hx y hy hxy
    have hx' := hK₀s.subset hx
    have hy' := hK₀s.subset hy
    exact hgi (K.convexHull_subset_space hs hx') (K.convexHull_subset_space hs hy')
      (Q.injOn (hmap hx') (hmap hy') ((hA hx').trans (hxy.trans (hA hy').symm)))
  have hf : K₀.AffineOnFaces A := K₀.affineOnFaces_affine A
  let T := hf.embeddedImage hAi
  have ht : s.image A ∈ T.faces :=
    (hf.image_mem_embeddedImage_iff hAi (K₀.subset_space hs₀)).mpr hs₀
  have hAiv : InjOn A (s : Set E) := hAi.mono (K₀.subset_space hs₀)
  obtain ⟨v0, v1, h01, ha⟩ := Finset.card_eq_two.mp ha2
  obtain ⟨v2, h2, hs'⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨has, by rw [ha2, hs3]⟩
  have hs'' : s = {v2, v0, v1} := by rw [← hs', ha]
  have hv0 : v0 ∈ s := by rw [hs'']; simp
  have hv1 : v1 ∈ s := by rw [hs'']; simp
  have hv2 : v2 ∈ s := by rw [hs'']; simp
  have h02 : v0 ≠ v2 := fun he => h2 (by rw [ha, ← he]; simp)
  have h12 : v1 ≠ v2 := fun he => h2 (by rw [ha, ← he]; simp)
  have h01A : A v0 ≠ A v1 := fun he => h01 (hAiv hv0 hv1 he)
  have h02A : A v0 ≠ A v2 := fun he => h02 (hAiv hv0 hv2 he)
  have h12A : A v1 ≠ A v2 := fun he => h12 (hAiv hv1 hv2 he)
  have hface : ({A v0, A v1, A v2} : Set V) = A '' (s : Set E) := by
    rw [hs'']
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, image_insert_eq, image_singleton,
      mem_insert_iff, mem_singleton_iff]
    tauto
  have hedge : ({A v0, A v1} : Set V) = A '' (a : Set E) := by
    rw [ha]
    simp only [Finset.coe_insert, Finset.coe_singleton, image_insert_eq, image_singleton]
  have ht' : ({A v0, A v1, A v2} : Finset V) ∈ T.faces := by
    convert ht using 1
    apply Finset.coe_injective
    simpa only [Finset.coe_insert, Finset.coe_singleton, Finset.coe_image] using hface
  have h := T.exists_actual_returning_component_bigons G hG hdim h01A h02A h12A ht'
    (by simpa only [hface] using hGT) (by simpa only [hface] using hfinite)
    (by simpa only [hface] using hinterior) (by simpa only [hface] using hexterior)
    (by simpa only [hedge] using hreturn)
  dsimp only at h
  rw [hface, hedge] at h
  obtain ⟨F, R, n, e, P, hRF, hFR, _, _, _, hrest⟩ := h
  exact ⟨F, R, n, e, P, hRF, hFR, hrest⟩

end PoincareConjecture.M76
