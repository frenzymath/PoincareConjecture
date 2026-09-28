import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalFamilyEdgeCofaceMotion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.FiniteSphereSystemCofaceCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ProtectedFamilyVertexPosition

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_sphere_system_finite_edge_coface_position
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {Z : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K M : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hMK : M ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g))
    (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ M.space)
    (hSZ : Disjoint (⋃ i, S i) Z) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ Disjoint C Z ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) ∧
      Disjoint (F '' (⋃ i, S i)) (g '' K.vertices) ∧
      ∀ a ∈ K.faces, a.card = 2 →
        ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite ∧
        HasOriginalEdgeCofaceCharts e (F '' (⋃ i, S i)) K g a := by
  classical
  have hV : (g '' K.vertices).Finite := by
    apply Set.Finite.image
    rw [K.vertices_eq]
    exact hK.biUnion (fun a _ => a.finite_toSet)
  obtain ⟨F₀, C₀, hC₀, hC₀Z, hF₀out, hF₀PL, hF₀inv, hS₀, hV₀⟩ :=
    exists_protected_sphere_system_vertex_position S sS hdis hcover he hZ hSZ hV.toFinset
  have hV₀' : Disjoint (F₀ '' (⋃ i, S i)) (g '' K.vertices) := by simpa using hV₀
  let P (T : Finset (Finset E)) : Prop :=
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ Disjoint C Z ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) ∧
      Disjoint (F '' (⋃ i, S i)) (g '' K.vertices) ∧
      ∀ a ∈ T, ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite ∧
        HasOriginalEdgeCofaceCharts e (F '' (⋃ i, S i)) K g a
  have hposition (T : Finset (Finset E)) :
      (∀ a ∈ T, a ∈ K.faces ∧ a.card = 2) → P T := by
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨F₀, C₀, hC₀, hC₀Z, hF₀out, hF₀PL, hF₀inv, hS₀, hV₀', by simp⟩
    | @insert a T haT ih =>
      intro hT
      have haK := (hT a (Finset.mem_insert_self _ _)).1
      have hac := (hT a (Finset.mem_insert_self _ _)).2
      have hT' (b : Finset E) (hb : b ∈ T) : b ∈ K.faces ∧ b.card = 2 :=
        hT b (Finset.mem_insert_of_mem hb)
      obtain ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, ⟨sF⟩, hFV, hedges⟩ := ih hT'
      have hFZ : Disjoint (F '' (⋃ i, S i)) Z := by
        apply disjoint_left.mpr
        rintro x ⟨y, hy, hxy⟩ hxZ
        have hfix : F x = x := hFout (fun hc => disjoint_left.mp hCZ hc hxZ)
        have hyx : y = x := F.injective (hxy.trans hfix.symm)
        exact disjoint_left.mp hSZ (hyx ▸ hy) hxZ
      by_cases haM : a ∈ M.faces
      · have haZ : g '' convexHull ℝ (a : Set E) ⊆ Z := by
          rintro _ ⟨x, hx, rfl⟩
          exact (hmark x (K.convexHull_subset_space haK hx)).mpr
            (M.convexHull_subset_space haM hx)
        have hempty : (F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E)) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          exact fun x hx => disjoint_left.mp hFZ hx.1 (haZ hx.2)
        refine ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, ⟨sF⟩, hFV, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · refine ⟨hempty.symm ▸ finite_empty, ?_⟩
          intro y hy
          exact (disjoint_left.mp hFZ hy.1 (haZ hy.2)).elim
        · exact hedges b hb
      · obtain ⟨p, q, hpq, haeq⟩ := Finset.card_eq_two.mp hac
        subst a
        obtain ⟨G, D, hD, hDZ, hDV, hDE, hGout, hGPL, hGinv, hSG, hfinite,
            hcharts⟩ :=
          exists_original_sphere_system_edge_coface_motion (fun i => F '' S i) sF
            (by
              intro i j hij
              apply disjoint_left.mpr
              rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
              exact disjoint_left.mp (hdis hij) ha (F.injective (hbx.trans hax.symm) ▸ hb))
            hcover he K M hK hMK g hgc hgi hstars hZ hmark
            (by simpa only [← image_iUnion] using hFV) p q hpq haK haM
        rw [← image_iUnion] at hfinite hcharts
        have himage : (F.trans G) '' (⋃ i, S i) = G '' (F '' (⋃ i, S i)) := by
          rw [image_image]
          rfl
        have hPL := original_PL_motion_trans e hcover F G hFPL hGPL
        have hinv := original_PL_motion_trans e hcover G.symm F.symm hGinv hFinv
        refine ⟨F.trans G, C ∪ D, hC.union hD,
          disjoint_union_left.mpr ⟨hCZ, hDZ⟩, ?_, hPL, hinv,
          ⟨fun i => Classical.choice ((sS i).nonempty_image (F.trans G) hcover hPL)⟩, ?_, ?_⟩
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
            have hDb := hDE b (hT' b hb).1 (hT' b hb).2 hbne
            have hfix (x : X) (hx : x ∈ g '' convexHull ℝ (b : Set E)) : G x = x :=
              hGout (fun hd => disjoint_left.mp hDb hd hx)
            have hsame : (G '' (F '' (⋃ i, S i))) ∩ (g '' convexHull ℝ (b : Set E)) =
                (F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (b : Set E)) := by
              ext x
              constructor
              · rintro ⟨⟨y, hy, hxy⟩, hxb⟩
                have hyx : y = x := G.injective (hxy.trans (hfix x hxb).symm)
                exact ⟨hyx ▸ hy, hxb⟩
              · rintro ⟨hx, hxb⟩
                exact ⟨⟨x, hx, hfix x hxb⟩, hxb⟩
            refine ⟨hsame.symm ▸ (hedges b hb).1, ?_⟩
            exact (hedges b hb).2.image_of_disjoint_support G hD.isClosed hDb hGout
  let T := hK.toFinset.filter (fun a => a.card = 2)
  have hT (a : Finset E) (ha : a ∈ T) : a ∈ K.faces ∧ a.card = 2 := by
    simpa only [T, Finset.mem_filter, Set.Finite.mem_toFinset] using ha
  obtain ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hsF, hFV, hedges⟩ := hposition T hT
  refine ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hsF, hFV, ?_⟩
  intro a ha hac
  exact hedges a (by simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, ha, hac,
    and_self])

end PoincareConjecture.M76
