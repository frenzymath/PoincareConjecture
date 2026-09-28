import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryStarBall
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSurfaceIncidence

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

omit [FiniteDimensional ℝ E] in
private theorem barycentric_star_face_containment
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {p : E} (hp : p ∈ K.vertices) :
    ∀ s ∈ (K.barycentricSubdivision.closedStar p).faces,
      ∃ t ∈ (K.closedStar p).faces,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  intro s hs
  obtain ⟨a, ha, hchain, rfl, hpa⟩ :=
    (K.barycentricSubdivision_closedStar_faces hp s).mp hs
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  refine ⟨m.val, ⟨m.property, ?_⟩, convexHull_min ?_ (convex_convexHull ℝ _)⟩
  · simpa only [Finset.insert_eq_of_mem (hpa m hm)] using m.property
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have him : i.val ⊆ m.val := by
      rcases hchain i hi m hm with h | h
      · exact h
      · exact hmax hi h
    exact convexHull_mono him
      (i.val.centroid_mem_convexHull (K.nonempty_of_mem_faces i.property))

theorem exists_original_boundary_dual_half_ball
    (K L : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype L.faces]
    (hLK : L ≤ K) {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (HB : L.space ≃ₜ frontier R)
    (hHB : ∀ z : L.space, (HB z : X) = (g z : X))
    {p : E} (hp : p ∈ L.vertices)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (C : Set V3) (A : V3 →ₗ[ℝ] ℝ) (v : V3)
      (G : (K.barycentricDualBlock {p}).space ≃ₜ (C ∩ {x | 0 ≤ A x} : Set V3)),
      A v = 1 ∧ IsCompact C ∧ Convex ℝ C ∧ (0 : V3) ∈ interior C ∧
      (∃ J : SimplicialComplex ℝ V3, J.faces.Finite ∧ J.space = C) ∧
      IsFinitePLBallPair V3 (K.barycentricDualBlock {p}).space
        (((K.barycentricDualBlock {p}).link p).space ∪
          (L.barycentricDualBlock {p}).space) ∧
      G.IsFinitePL ∧
      (∀ x : (K.barycentricDualBlock {p}).space,
        (x : E) ∈ ((K.barycentricDualBlock {p}).link p).space ↔
          (G x : V3) ∈ frontier C) ∧
      ∀ x : (K.barycentricDualBlock {p}).space,
        A (G x : V3) = 0 ↔ (x : E) ∈ (L.barycentricDualBlock {p}).space := by
  classical
  have hpK : p ∈ K.vertices := hLK hp
  have hcontain := barycentric_star_face_containment K hpK
  have hstar : (K.barycentricSubdivision.closedStar p).space ⊆
      (K.closedStar p).space := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp hz
    obtain ⟨t, ht, hst⟩ := hcontain s hs
    exact (K.closedStar p).convexHull_subset_space ht (hst hzs)
  have hbar := K.barycentricSubdivision_isSubdivision.space_eq
  let Hbar : R ≃ₜ K.barycentricSubdivision.space :=
    H.trans (Homeomorph.setCongr hbar.symm)
  have hgbar (z : K.barycentricSubdivision.space) :
      (g z : X) = (Hbar.symm z : X) :=
    hg ⟨z, hbar.subset z.property⟩
  have hpb : (g p : X) ∈ frontier R := by
    rw [← hHB ⟨p, L.vertices_subset_space hp⟩]
    exact (HB ⟨p, L.vertices_subset_space hp⟩).property
  have h := exists_original_boundary_star_half_ball K.barycentricSubdivision
    K.barycentricSubdivision_finite Hbar g hgbar
    (K.vertices_subset_barycentricSubdivision_vertices hpK) hpb B
    (fun z hz => hsource (hstar hz)) (hface.of_face_containment hcontain) hregion
  rw [← K.barycentricDualBlock_singleton_eq_closedStar hpK] at h
  obtain ⟨C, A, v, G, hv, hC, hcv, hC0, hpoly, hpair, hG, hGb, hG0⟩ := h
  have hginj : InjOn (fun z => (g z : X)) K.space := by
    intro z hz w hw he
    apply congrArg Subtype.val (H.symm.injective (show
      H.symm (⟨z, hz⟩ : K.space) = H.symm ⟨w, hw⟩ from ?_))
    exact Subtype.ext ((hg ⟨z, hz⟩).symm.trans (he.trans (hg ⟨w, hw⟩)))
  have hfront (z : E) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier R ↔ z ∈ L.space := by
    constructor
    · intro hzb
      obtain ⟨w, hw⟩ := HB.surjective ⟨g z, hzb⟩
      have hgw : (g w : X) = (g z : X) :=
        (hHB w).symm.trans (congrArg Subtype.val hw)
      have hwz := hginj (SimplicialComplex.space_subset_of_le hLK w.property) hz hgw
      exact hwz ▸ w.property
    · intro hzL
      rw [← hHB ⟨z, hzL⟩]
      exact (HB ⟨z, hzL⟩).property
  have hNK : (K.barycentricDualBlock {p}).space ⊆ K.space :=
    (SimplicialComplex.space_subset_of_le (K.barycentricDualBlock_le {p})).trans
      hbar.subset
  have hmarks : (K.barycentricDualBlock {p}).space ∩
      {z | (g z : X) ∈ frontier R} = (L.barycentricDualBlock {p}).space := by
    rw [← K.barycentricDualBlock_space_inter_subcomplex L hLK {p}]
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      exact ⟨hz, (hfront z (hNK hz)).mp hzb⟩
    · rintro ⟨hz, hzL⟩
      exact ⟨hz, (hfront z (hNK hz)).mpr hzL⟩
  rw [hmarks] at hpair
  refine ⟨C, A, v, G, hv, hC, hcv, hC0, hpoly, hpair, hG, hGb, ?_⟩
  intro x
  rw [hG0 x, ← hmarks]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

end PoincareConjecture.M76
