import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexDisks
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualVertexFaceContainment
import PoincareConjecture.Proofs.M76.Mathlib.SubdivisionVertices












set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem exists_original_local_boundary_dual
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hDK : D ≤ K) {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ D.vertices)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hfront : ∀ z ∈ (K.closedStar p).space,
      (g z : X) ∈ frontier R ↔ z ∈ D.space)
    (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (hv : ell.contLinear v = 1)
    (hhalf : ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    Nonempty (BoundaryVertexHalfBall K D p) := by
  classical
  have hpK : p ∈ K.vertices := hDK hp
  have hpstar : p ∈ (K.closedStar p).vertices := by
    change {p} ∈ K.faces ∧ insert p {p} ∈ K.faces
    exact ⟨hpK, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      using (show {p} ∈ K.faces from hpK)⟩
  have hpb : (g p : X) ∈ frontier R :=
    (hfront p ((K.closedStar p).vertices_subset_space hpstar)).mpr
      (D.vertices_subset_space hp)
  let J := K.barycentricSubdivision
  have hJs : J.space = K.space := K.barycentricSubdivision_isSubdivision.space_eq
  let H' : R ≃ₜ J.space := H.trans (Homeomorph.setCongr hJs.symm)
  have hg' (z : J.space) : (g z : X) = (H'.symm z : X) :=
    hg ⟨z, hJs.subset z.property⟩
  have hpJ : p ∈ J.vertices := K.barycentricSubdivision_isSubdivision.vertices_subset hpK
  have hdual : K.barycentricDualBlock {p} = J.closedStar p :=
    K.barycentricDualBlock_singleton_eq_closedStar hpK
  have hcontain : ∀ s ∈ (J.closedStar p).faces,
      ∃ t ∈ (K.closedStar p).faces,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
    rw [← hdual]
    exact fun _ hs => K.exists_original_star_face_of_vertex_dual_face hpK hs
  have hstar : (J.closedStar p).space ⊆ (K.closedStar p).space := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hst⟩ := hcontain s hs
    exact (K.closedStar p).convexHull_subset_space ht (hst hzs)
  have h := exists_original_boundary_star_half_ball J K.barycentricSubdivision_finite
    H' g hg' hpJ hpb B (fun _ hz => hsource (hstar hz))
    (hface.of_face_containment hcontain) (Or.inr ⟨ell, v, hv, hhalf⟩)
  rw [← hdual] at h
  obtain ⟨C, A, w, G, hw, hC, hcv, hC0, hpoly, hball, hG, hGb, hG0⟩ := h
  have hdualstar : (K.barycentricDualBlock {p}).space ⊆ (K.closedStar p).space := by
    rw [hdual]
    exact hstar
  have hmarks : (K.barycentricDualBlock {p}).space ∩
      {z | (g z : X) ∈ frontier R} = (D.barycentricDualBlock {p}).space := by
    rw [← K.barycentricDualBlock_space_inter_subcomplex D hDK {p}]
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      exact ⟨hz, (hfront z (hdualstar hz)).mp hzb⟩
    · rintro ⟨hz, hzD⟩
      exact ⟨hz, (hfront z (hdualstar hz)).mpr hzD⟩
  rw [hmarks] at hball
  refine ⟨⟨C, A, w, G, hw, hC, hcv, hC0, hpoly, hball, hG, hGb, ?_⟩⟩
  intro x
  rw [hG0 x, ← hmarks]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

end PoincareConjecture.M76
