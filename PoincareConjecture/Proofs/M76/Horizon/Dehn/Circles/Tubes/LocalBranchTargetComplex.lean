import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalBranchTransition
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceStarNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)


theorem convex_subset_coordinate_cross {S : Set V3} (hS : Convex ℝ S)
    (hcross : ∀ z ∈ S, z 0 = 0 ∨ z 1 = 0) :
    (∀ z ∈ S, z 0 = 0) ∨ ∀ z ∈ S, z 1 = 0 := by
  classical
  by_cases h : ∀ z ∈ S, z 0 = 0
  · exact Or.inl h
  push Not at h
  obtain ⟨a, ha, ha0⟩ := h
  have ha1 := (hcross a ha).resolve_left ha0
  right
  intro b hb
  by_contra hb1
  have hb0 := (hcross b hb).resolve_right hb1
  have hm := hcross _ (hS ha hb (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha1, hb0, mul_zero, add_zero,
    zero_add] at hm
  rcases hm with hm | hm
  · exact ha0 (by linarith)
  · exact hb1 (by linarith)



theorem local_crossing_vertexSubcomplex_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K U A : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hUK : U ≤ K) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ U.vertices) → s ∈ U.faces)
    {c : E → V3} (hc : K.AffineOnFaces c) (R : Set E)
    (hU : ∀ z ∈ K.space, z ∈ U.space ↔ z ∈ R ∧ (c z 0 = 0 ∨ c z 1 = 0))
    (hA : ∀ z ∈ K.space, z ∈ A.space ↔ z ∈ R ∧ c z 0 = 0 ∧ c z 1 = 0)
    (j : Fin 2) :
    (K.vertexSubcomplex {z | z ∈ R ∧ c z j.castSucc = 0}).space =
      K.space ∩ {z | z ∈ R ∧ c z j.castSucc = 0} := by
  classical
  let V := {z | z ∈ R ∧ c z j.castSucc = 0}
  have hvU : ∀ v ∈ K.vertices, v ∈ V → v ∈ U.vertices := by
    intro v hv hvV
    have hvK := K.vertices_subset_space hv
    have hvUs : v ∈ U.space := (hU v hvK).mpr ⟨hvV.1, by
      fin_cases j <;> simp_all [V]⟩
    obtain ⟨t, ht, hvt⟩ := SimplicialComplex.mem_space_iff.mp hvUs
    exact U.down_closed ht (Finset.singleton_subset_iff.mpr
      ((K.vertex_mem_convexHull_iff hv (hUK ht)).mp hvt)) (Finset.singleton_nonempty v)
  apply Subset.antisymm
  · intro z hz
    obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp hz
    have hsU := hfull s hs.1 (fun v hv => hvU v (K.face_subset_vertices hs.1 hv) (hs.2 v hv))
    have hzK := K.convexHull_subset_space hs.1 hzs
    refine ⟨hzK, ((hU z hzK).mp (U.convexHull_subset_space hsU hzs)).1, ?_⟩
    obtain ⟨b, hb⟩ := hc s hs.1
    have hz0 := AffineMap.eqOn_affineSpan
      (f := (LinearMap.proj j.castSucc : V3 →ₗ[ℝ] ℝ).toAffineMap.comp b.toAffineMap)
      (g := AffineMap.const ℝ E 0)
      (fun v hv => (congrArg (fun q : V3 => q j.castSucc) (hb (subset_convexHull ℝ _ hv))).symm.trans
        (hs.2 v hv).2) (convexHull_subset_affineSpan _ hzs)
    exact (congrArg (fun q : V3 => q j.castSucc) (hb hzs)).trans hz0
  · rintro z ⟨hzK, hzR, hzj⟩
    obtain ⟨s, hs, hzs, hmin, _⟩ := K.exists_minimal_faceStar_neighborhood_of_finite hK ⟨z, hzK⟩
    have hface (B : SimplicialComplex ℝ E) (hBK : B ≤ K) (hzB : z ∈ B.space) : s ∈ B.faces := by
      obtain ⟨t, ht, hzt⟩ := SimplicialComplex.mem_space_iff.mp hzB
      exact B.down_closed ht (hmin t (hBK ht) hzt) (K.nonempty_of_mem_faces hs)
    have hzU : z ∈ U.space := (hU z hzK).mpr ⟨hzR, by fin_cases j <;> simp_all⟩
    have hsU := hface U hUK hzU
    obtain ⟨b, hb⟩ := hc s hs
    have hplanes := convex_subset_coordinate_cross
      ((convex_convexHull ℝ (s : Set E)).affine_image b) (by
        rintro q ⟨w, hw, rfl⟩
        change b w 0 = 0 ∨ b w 1 = 0
        rw [← hb hw]
        exact ((hU w (K.convexHull_subset_space hs hw)).mp (U.convexHull_subset_space hsU hw)).2)
    have hone : (∀ w ∈ convexHull ℝ (s : Set E), c w 0 = 0) ∨
        ∀ w ∈ convexHull ℝ (s : Set E), c w 1 = 0 := by
      rcases hplanes with h | h
      · exact Or.inl (fun w hw => (congrArg (fun q : V3 => q 0) (hb hw)).trans (h _ ⟨w, hw, rfl⟩))
      · exact Or.inr (fun w hw => (congrArg (fun q : V3 => q 1) (hb hw)).trans (h _ ⟨w, hw, rfl⟩))
    have hzother (hother : c z j.rev.castSucc = 0) : s ∈ A.faces := by
      apply hface A hAK
      apply (hA z hzK).mpr
      fin_cases j <;> simp_all
    refine SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, ?_⟩, hzs⟩
    intro v hv
    have hvh := subset_convexHull ℝ (s : Set E) hv
    have hvK := K.convexHull_subset_space hs hvh
    refine ⟨((hU v hvK).mp (U.convexHull_subset_space hsU hvh)).1, ?_⟩
    rcases hone with h0 | h1
    · fin_cases j
      · exact h0 v hvh
      · exact ((hA v hvK).mp (A.convexHull_subset_space (hzother (h0 z hzs)) hvh)).2.2
    · fin_cases j
      · exact ((hA v hvK).mp (A.convexHull_subset_space (hzother (h1 z hzs)) hvh)).2.1
      · exact h1 v hvh



theorem ComponentBranchModel.exists_marked_raw_star
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : (Fin 2 → ℝ) → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    ∃ (x y : Fin 2 → ℝ) (C : RawCrossingChart e f R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      (∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
          C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0) ∧
      ∀ j : Fin 2,
        ((D.complex.closedStar p).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
        (D.complex.closedStar p).space ∩
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0} := by
  classical
  obtain ⟨q, hmap, hface⟩ := D.selected_stars p hp
  obtain ⟨x, y, C, _, hB, hBC⟩ := D.raw_charts q
  let K := D.complex.closedStar p
  have hKD : K ≤ D.complex := fun _ hs => hs.1
  have hKs := SimplicialComplex.space_subset_of_le hKD
  have hKC : MapsTo (fun z ↦ (D.inverse z : X)) K.space C.chart.source :=
    fun _ hz => hBC (hmap hz)
  have hCface : K.AffineOnFaces (fun z ↦ C.chart (D.inverse z)) := by
    simpa only [hB] using hface
  have hUspace := D.complex.space_inf_eq_inter_of_le D.diskImage K D.diskImage_le hKD
  have hAspace := D.complex.space_inf_eq_inter_of_le D.axis K D.axis_le hKD
  have hfull : ∀ s ∈ K.faces,
      (∀ v ∈ s, v ∈ (D.diskImage ⊓ K).vertices) → s ∈ (D.diskImage ⊓ K).faces := by
    intro s hs hv
    exact ⟨D.diskImage_full s (hKD hs) (fun v hvs => (hv v hvs).1), hs⟩
  have haxis (z : D.sample → ℝ × V3) (hz : z ∈ K.space) :
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ f '' old.pieces i := by
    rw [D.axis_space]
    constructor
    · rintro ⟨a, ha, haz⟩
      refine ⟨a, ha, ?_⟩
      exact (D.graph_separates _ (D.inverse z).property _
        ((D.graph_inverse z (hKs hz)).trans haz.symm)).symm
    · rintro ⟨a, ha, haz⟩
      refine ⟨a, ha, ?_⟩
      change D.graph (f a) = z
      rw [haz, D.graph_inverse z (hKs hz)]
  have hCA (z : D.sample → ℝ × V3) (hz : z ∈ K.space) :
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0 := by
    rw [haxis z hz]
    simpa only [hB] using D.chart_axis q (D.inverse z) (hmap hz)
  refine ⟨x, y, C, hKC, hCface, hCA, fun j => ?_⟩
  apply local_crossing_vertexSubcomplex_space K (D.diskImage ⊓ K) (D.axis ⊓ K)
    (SimplicialComplex.finite_closedStar_faces D.complex_finite p)
    inf_le_right inf_le_right hfull hCface {z | (D.inverse z : X) ∈ R}
  · intro z hz
    rw [hUspace, mem_inter_iff, and_iff_left hz, D.mem_diskImage z (hKs hz)]
    exact C.disk_image_iff _ (hKC hz)
  · intro z hz
    rw [hAspace, mem_inter_iff, and_iff_left hz]
    exact hCA z hz

end PoincareConjecture.M76.Dehn
