import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalDiskConeHomotopy
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalChartTriangleHeights
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalMarkedFanHeights
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.PlanarCofaces
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.FiniteFamily

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_disk_frontier_polygons
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
    [TopologicalSpace X] [Nonempty X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hdim : Module.finrank ℝ E = 2)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (f : E → X) (hfY : MapsTo f K.space Y)
    (B : K.vertices → OpenPartialHomeomorph X V3)
    (hcompat : ∀ v i, (e i).symm.trans (B v) ∈ piecewiseAffineGroupoid V3)
    (hsource : ∀ v : K.vertices, MapsTo f (K.closedStar v).space (B v).source)
    (hcoord : ∀ v : K.vertices, (K.closedStar v).AffineOnFaces (B v ∘ f))
    (hkind : ∀ v, Disjoint (B v).source F ∨ ∃ ell : V3 →ᴬ[ℝ] ℝ,
      (∀ y ∈ (B v).source, y ∈ N ↔ 0 ≤ ell (B v y)) ∧
      ∀ y ∈ (B v).source, y ∈ F ↔ ell (B v y) = 0)
    (hboundary : ∀ x ∈ frontier K.space, f x ∉ F) :
    ∃ (G : C(I × K.space, X)) (g : E → X) (S : Set (Set E)),
      (∀ z, G z ∈ Y) ∧ (∀ x : K.space, G (0, x) = f x) ∧
      (∀ x : K.space, G (1, x) = g x) ∧
      (∀ (t : I) (x : K.space), (x : E) ∈ frontier K.space → G (t, x) = f x) ∧
      PolyhedralPLInCharts e g K.space ∧ S.Finite ∧
      (∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon E (n + 3),
        Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s) ∧
      S.PairwiseDisjoint id ∧ K.space ∩ g ⁻¹' F = ⋃ s ∈ S, s ∧
      ∀ s ∈ S, s ⊆ interior K.space := by
  classical
  obtain ⟨a, b, v, T0, R, L, Q, C, T, G0, G, g0, g, p, hab, hpair, hv,
    hT0, hT0K, hT0S, hR, hRT, hL, hQ, hT, hTK, hTfaces, hC,
    hp0, hpY, hpfix, hpoff, hg0off, hcross, hnozero, hline, hend,
    hG00, hG01, hrestrict, hfixed, hGY, hG0, hG1, hg⟩ :=
    hN.exists_original_disk_cone_homotopy K hY hcut hK hdim hcv hne f hfY B
      hcompat hsource hcoord hkind
  obtain ⟨hGfixed, hgf, hgoff⟩ := hfixed hboundary
  have hCS := fun s => (hC s).2.1
  have hLC := fun s => (hC s).2.2.1
  have hCT := fun s => (hC s).2.2.2.1
  have hCvertices := fun s => (hC s).2.2.2.2.1
  have hCfaces := fun s => (hC s).2.2.2.2.2.2.1
  have hCcoords := fun s => (hC s).2.2.2.2.2.2.2.1
  have hCapex := fun s => (hC s).2.2.2.2.2.2.2.2.1
  have hCboundary := fun s => (hC s).2.2.2.2.2.2.2.2.2.1
  have hCsource := fun s => (hC s).2.2.2.2.2.2.2.2.2.2
  obtain ⟨ell, owner, A, hell, hside, howner, hformula, hzero, hcompatA, hzeroSet⟩ :=
    T.exists_original_chart_triangle_heights hT hdim (hTK.symm ▸ hcv) (hTK.symm ▸ hne)
      C hTfaces g (fun s => B (v s)) N F hCsource hCcoords (fun s => by
        rcases hkind (v s) with hd | ⟨ell, hN, hF⟩
        · exact Or.inl hd
        · exact Or.inr ⟨ell.toAffineMap, hN, hF⟩)
  have hformulaC (s : {s : K.faces // s.val.card = 3}) (z : Finset E)
      (hz : z ∈ (C s).faces) (hc : z.card = 3) :=
    K.original_chart_triangle_formula T hdim C (fun s => (hCS s).subset) g
      (fun s => B (v s)) ell owner A howner hformula (hCT s hz) hz hc
  have hQhull (k : {s : K.faces // s.val.card = 2}) :
      (Q k).space = convexHull ℝ (k.val.val : Set E) := by
    rw [← hpair k, Finset.coe_pair, convexHull_pair]
    exact (hQ k).2.1
  have hedgeT (k : {s : K.faces // s.val.card = 2}) :
      segment ℝ (a k : E) (b k : E) ⊆ T0.space :=
    fun _ hx => hT0S.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)
  have hend1 (k : {s : K.faces // s.val.card = 2}) :
      g0 (a k) = p (a k) 1 ∧ g0 (b k) = p (b k) 1 := by
    have hh := hend k 1 (hedgeT k (left_mem_segment ℝ _ _)) (hedgeT k (right_mem_segment ℝ _ _))
    exact ⟨(hG01 _).symm.trans hh.1, (hG01 _).symm.trans hh.2⟩
  have hBsource (k : {s : K.faces // s.val.card = 2}) :
      MapsTo g0 (segment ℝ (a k : E) (b k : E)) (B (a k)).source := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (segment_eq_image_lineMap ℝ (a k : E) (b k : E)).subset hx
    have hh := (hline k 1 ⟨r, hr⟩ (hedgeT k (lineMap_mem_segment ℝ _ _ hr))).1
    rwa [hG01] at hh
  have hBline (k : {s : K.faces // s.val.card = 2}) (r : I) :
      B (a k) (g0 (AffineMap.lineMap (a k : E) (b k : E) (r : ℝ))) =
        AffineMap.lineMap (B (a k) (g0 (a k))) (B (a k) (g0 (b k))) (r : ℝ) := by
    have hh := (hline k 1 r (hedgeT k (lineMap_mem_segment ℝ _ _ r.property))).2
    rw [hG01] at hh
    simpa only [← (hend1 k).1, ← (hend1 k).2] using hh
  have hmarked {q : E} (hq : q ∈ T.triangleZeroVertices A) : g q ∈ F := by
    obtain ⟨z, hz, _, hqz, hq0⟩ := hq.2
    exact (hzero z hz q (subset_convexHull ℝ _ hqz)).mp hq0
  have hfans := fun q : T.triangleZeroVertices A =>
    K.exists_original_marked_fan_heights hK hdim R T L C Q (fun s => (hL s).1)
      (fun s => (hL s).2.1) (fun k => (hQ k).1) hQhull (fun s => (hC s).1)
      hCS hLC hCvertices hCfaces hTK hTfaces g0 g N F hCboundary
      (fun x hx => hg0off ⟨x, hx⟩) hCapex hgoff a b hab hpair (fun k => B (a k))
      hBsource hBline (fun k => hkind (a k)) (fun s => B (v s)) ell A
      hCsource hell hside hformulaC q.property.1 (hmarked q.property)
  have hnozeroA : ∀ z ∈ T.faces, z.card = 2 → ∃ q ∈ z, q ∉ T.triangleZeroVertices A := by
    intro z hz hc
    obtain ⟨q, hq, hqF⟩ := hnozero z hz hc
    exact ⟨q, hq, fun hm => hqF (hmarked hm)⟩
  have hcofaces := T.triangleCrossingEdges_two_cofaces_of_boundary_avoids hT hdim A g F
    (fun z hz _ => hzero z hz) (hTK.symm ▸ hgoff)
  obtain ⟨S, hS, hpolygons, hdisjoint, hcover, hsub, hinterior⟩ :=
    T.exists_finite_triangleSlice_polygon_family hcompatA hT hnozeroA hcofaces hfans
  have hzeroInt : T.triangleZeroSet A ⊆ interior T.space := by
    intro x hx
    obtain ⟨hxT, hxF⟩ := hzeroSet.subset hx
    by_contra hn
    exact hgoff x (hTK ▸ (show x ∈ frontier T.space from ⟨subset_closure hxT, hn⟩)) hxF
  refine ⟨G, g, S, hGY, hG0, hG1, hGfixed, hg, hS, hpolygons, hdisjoint, ?_, ?_⟩
  · exact (congrArg (fun s : Set E => s ∩ g ⁻¹' F) hTK).symm.trans (hzeroSet.symm.trans hcover)
  · simpa only [hTK] using hinterior hzeroInt

end PoincareConjecture.M76
