import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Initial.Cofaces
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Initial.Vertices












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_protected_planar_finite_edge_coface_position
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Z : Set X}
    (Source : SimplicialComplex ℝ (ℝ × ℝ)) (hSource : Source.faces.Finite)
    {f : (ℝ × ℝ) → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K M : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hMK : M ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g))
    (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ M.space)
    (hprotectedV : Disjoint (f '' Source.space ∩ Z) (g '' K.vertices))
    (eligible : Finset E → Prop)
    (hprotectedE : ∀ a ∈ M.faces, a.card = 2 → eligible a →
      (f '' Source.space ∩ (g '' convexHull ℝ (a : Set E))).Finite ∧
        HasOriginalEdgeCofaceCharts e (f '' Source.space) K g a) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ Disjoint C Z ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      PolyhedralPLInCharts e (F ∘ f) Source.space ∧
      Disjoint (F '' (f '' Source.space)) (g '' K.vertices) ∧
      ∀ a ∈ K.faces, a.card = 2 → eligible a →
        ((F '' (f '' Source.space)) ∩ (g '' convexHull ℝ (a : Set E))).Finite ∧
        HasOriginalEdgeCofaceCharts e (F '' (f '' Source.space)) K g a := by
  classical
  have hV : (g '' K.vertices).Finite := by
    apply Set.Finite.image
    rw [K.vertices_eq]
    exact hK.biUnion (fun a _ => a.finite_toSet)
  obtain ⟨F₀, C₀, hC₀, hC₀Z, hF₀out, hF₀PL, hF₀inv, hS₀, hV₀⟩ :=
    exists_protected_planar_vertex_position Source hSource hf hcover he hZ hV.toFinset
      (by simpa using hprotectedV)
  have hV₀' : Disjoint (F₀ '' (f '' Source.space)) (g '' K.vertices) := by simpa using hV₀
  let P (T : Finset (Finset E)) : Prop :=
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ Disjoint C Z ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      PolyhedralPLInCharts e (F ∘ f) Source.space ∧
      Disjoint (F '' (f '' Source.space)) (g '' K.vertices) ∧
      ∀ a ∈ T, ((F '' (f '' Source.space)) ∩ (g '' convexHull ℝ (a : Set E))).Finite ∧
        HasOriginalEdgeCofaceCharts e (F '' (f '' Source.space)) K g a
  have hposition (T : Finset (Finset E)) :
      (∀ a ∈ T, a ∈ K.faces ∧ a.card = 2 ∧ eligible a) → P T := by
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨F₀, C₀, hC₀, hC₀Z, hF₀out, hF₀PL, hF₀inv, hS₀, hV₀', by simp⟩
    | @insert a T haT ih =>
      intro hT
      have haK := (hT a (Finset.mem_insert_self _ _)).1
      have hac := (hT a (Finset.mem_insert_self _ _)).2.1
      have hae := (hT a (Finset.mem_insert_self _ _)).2.2
      have hT' (b : Finset E) (hb : b ∈ T) : b ∈ K.faces ∧ b.card = 2 ∧ eligible b :=
        hT b (Finset.mem_insert_of_mem hb)
      obtain ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hfF, hFV, hedges⟩ := ih hT'
      by_cases haM : a ∈ M.faces
      · have haZ : g '' convexHull ℝ (a : Set E) ⊆ Z := by
          rintro _ ⟨x, hx, rfl⟩
          exact (hmark x (K.convexHull_subset_space haK hx)).mpr
            (M.convexHull_subset_space haM hx)
        have hCedge : Disjoint C (g '' convexHull ℝ (a : Set E)) :=
          hCZ.mono_right haZ
        have hfix (x : X) (hx : x ∈ g '' convexHull ℝ (a : Set E)) : F x = x :=
          hFout (fun hc => disjoint_left.mp hCedge hc hx)
        have hsame : F '' (f '' Source.space) ∩ g '' convexHull ℝ (a : Set E) =
            f '' Source.space ∩ g '' convexHull ℝ (a : Set E) := by
          ext x
          constructor
          · rintro ⟨⟨y, hy, hyx⟩, hxe⟩
            exact ⟨F.injective (hyx.trans (hfix x hxe).symm) ▸ hy, hxe⟩
          · rintro ⟨hx, hxe⟩
            exact ⟨⟨x, hx, hfix x hxe⟩, hxe⟩
        refine ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hfF, hFV, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ⟨hsame.symm ▸ (hprotectedE b haM hac hae).1,
            (hprotectedE b haM hac hae).2.image_of_disjoint_support F hC.isClosed hCedge hFout⟩
        · exact hedges b hb
      · obtain ⟨p, q, hpq, haeq⟩ := Finset.card_eq_two.mp hac
        subst a
        have hFimage : (F ∘ f) '' Source.space = F '' (f '' Source.space) :=
          (image_image F f Source.space).symm
        obtain ⟨G, D, hD, hDZ, hDV, hDE, hGout, hGPL, hGinv, hSG, hfinite,
            hcharts⟩ :=
          exists_original_planar_edge_coface_motion Source hSource hfF
            hcover he K M hK hMK g hgc hgi hstars hZ hmark
            (by rw [hFimage]; exact hFV) p q hpq haK haM
        rw [hFimage] at hfinite hcharts
        have himage : (F.trans G) '' (f '' Source.space) = G '' (F '' (f '' Source.space)) := by
          rw [image_image G F]
          rfl
        have hPL := original_PL_motion_trans e hcover F G hFPL hGPL
        have hinv := original_PL_motion_trans e hcover G.symm F.symm hGinv hFinv
        refine ⟨F.trans G, C ∪ D, hC.union hD,
          disjoint_union_left.mpr ⟨hCZ, hDZ⟩, ?_, hPL, hinv,
          hf.comp_chart_homeomorph Source hSource (F.trans G) hcover hPL, ?_, ?_⟩
        · intro x hx
          change G (F x) = x
          rw [hFout (fun hc => hx (Or.inl hc))]
          exact hGout (fun hd => hx (Or.inr hd))
        · apply disjoint_left.mpr
          rintro x hx hxV
          obtain ⟨y, hy, hxy⟩ := himage.subset hx
          have hfix : G x = x := hGout (fun hd => disjoint_left.mp hDV hd hxV)
          have hyx : y = x := G.injective (hxy.trans hfix.symm)
          exact disjoint_left.mp hFV (hyx ▸ hy) hxV
        · intro b hb
          rw [himage]
          rcases Finset.mem_insert.mp hb with rfl | hb
          · simpa only [Finset.coe_pair, convexHull_pair] using And.intro hfinite hcharts
          · have hbne : b ≠ {p, q} := by
              intro h
              exact haT (h ▸ hb)
            have hDb := hDE b (hT' b hb).1 (hT' b hb).2.1 hbne
            have hfix (x : X) (hx : x ∈ g '' convexHull ℝ (b : Set E)) : G x = x :=
              hGout (fun hd => disjoint_left.mp hDb hd hx)
            have hsame : (G '' (F '' (f '' Source.space))) ∩ (g '' convexHull ℝ (b : Set E)) =
                (F '' (f '' Source.space)) ∩ (g '' convexHull ℝ (b : Set E)) := by
              ext x
              constructor
              · rintro ⟨⟨y, hy, hxy⟩, hxb⟩
                have hyx : y = x := G.injective (hxy.trans (hfix x hxb).symm)
                exact ⟨hyx ▸ hy, hxb⟩
              · rintro ⟨hx, hxb⟩
                exact ⟨⟨x, hx, hfix x hxb⟩, hxb⟩
            refine ⟨hsame.symm ▸ (hedges b hb).1, ?_⟩
            exact (hedges b hb).2.image_of_disjoint_support G hD.isClosed hDb hGout
  let T := hK.toFinset.filter (fun a => a.card = 2 ∧ eligible a)
  have hT (a : Finset E) (ha : a ∈ T) : a ∈ K.faces ∧ a.card = 2 ∧ eligible a := by
    simpa only [T, Finset.mem_filter, Set.Finite.mem_toFinset] using ha
  obtain ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hsF, hFV, hedges⟩ := hposition T hT
  refine ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hsF, hFV, ?_⟩
  intro a ha hac hae
  exact hedges a (by simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, ha, hac, hae,
    and_self])

end PoincareConjecture.M76
