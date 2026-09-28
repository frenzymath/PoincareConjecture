import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.VertexStarSideCharts
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexHalfBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.BarycentricStarCharts









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem exists_sphere_side_dual_half_ball
    (K P N : SimplicialComplex ℝ E)
    [Fintype K.faces] [Fintype P.faces] [Fintype N.faces]
    (hPK : P ≤ K) (hNP : N ≤ P) {p : E} (hp : p ∈ N.vertices)
    {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hzero : f p 0 = 0)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hside : (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0})
    (hboundary : ∀ x ∈ (K.closedStar p).space, x ∈ N.space ↔ f x 0 = 0) :
    Nonempty (BoundaryVertexHalfBall P N p) := by
  classical
  have hpP : p ∈ P.vertices := hNP hp
  have hpK : p ∈ K.vertices := hPK hpP
  have hKb := K.barycentricDualBlock_singleton_eq_closedStar hpK
  have hPb := P.barycentricDualBlock_singleton_eq_closedStar hpP
  have hbarstar := K.barycentric_closedStar_space_subset hpK
  have hfbar : (K.barycentricSubdivision.closedStar p).AffineOnFaces f :=
    hf.of_face_containment (K.barycentric_closedStar_face_containment hpK)
  have hinjbar : InjOn f (K.barycentricSubdivision.closedStar p).space := hinj.mono hbarstar
  have hintbar := K.mem_interior_image_barycentric_closedStar hpK hf hinj hint
  have hsidebar : (P.barycentricSubdivision.closedStar p).space =
      (K.barycentricSubdivision.closedStar p).space ∩ {x | 0 ≤ f x 0} := by
    have hinter := K.barycentricDualBlock_space_inter_subcomplex P hPK {p}
    rw [hKb, hPb] at hinter
    apply Subset.antisymm
    · intro x hx
      have hxK := (hinter.symm.subset hx).1
      have hxPstar := P.barycentric_closedStar_space_subset hpP hx
      exact ⟨hxK, (hside.subset hxPstar).2⟩
    · rintro x ⟨hx, hxheight⟩
      apply hinter.subset
      refine ⟨hx, ?_⟩
      have hxPstar := hside.symm.subset ⟨hbarstar hx, hxheight⟩
      exact space_subset_of_le (K := P.closedStar p) (L := P) (fun _ hs => hs.1) hxPstar
  have hdualzero : (P.barycentricDualBlock {p}).space ∩ {x | f x 0 = 0} =
      (N.barycentricDualBlock {p}).space := by
    have hinter := P.barycentricDualBlock_space_inter_subcomplex N hNP {p}
    calc
      (P.barycentricDualBlock {p}).space ∩ {x | f x 0 = 0} =
          (P.barycentricDualBlock {p}).space ∩ N.space := by
        ext x
        apply and_congr_right
        intro hx
        have hxPbar : x ∈ (P.barycentricSubdivision.closedStar p).space := hPb ▸ hx
        exact (hboundary x (hbarstar (hsidebar.subset hxPbar).1)).symm
      _ = (N.barycentricDualBlock {p}).space := hinter
  obtain ⟨C, v, H, hv, hC, hcv, hC0, hpoly, hball, hH, hlink, hheight⟩ :=
    K.barycentricSubdivision.exists_closedStar_side_chart P.barycentricSubdivision
      K.barycentricSubdivision_finite (P.barycentricSubdivision_mono hPK)
      (K.vertices_subset_barycentricSubdivision_vertices hpK) hfbar hinjbar
      hzero hintbar hsidebar
  have hlinkbar : (P.barycentricSubdivision.closedStar p).link p =
      P.barycentricSubdivision.link p := by
    ext s
    change ((s ∈ P.barycentricSubdivision.faces ∧ insert p s ∈ P.barycentricSubdivision.faces) ∧
      p ∉ s ∧ insert p s ∈ P.barycentricSubdivision.faces ∧
      insert p (insert p s) ∈ P.barycentricSubdivision.faces) ↔
      s ∈ P.barycentricSubdivision.faces ∧ p ∉ s ∧ insert p s ∈ P.barycentricSubdivision.faces
    simp only [Finset.insert_idem]
    tauto
  have hsource : (P.barycentricDualBlock {p}).space =
      (P.barycentricSubdivision.closedStar p).space := congrArg SimplicialComplex.space hPb
  have hlinkspace : ((P.barycentricDualBlock {p}).link p).space =
      (P.barycentricSubdivision.link p).space := by rw [hPb, hlinkbar]
  let G := (Homeomorph.setCongr hsource).trans H
  have hG : G.IsFinitePL := hH.setCongr hsource.symm rfl
  refine ⟨{
    body := C
    height := LinearMap.proj 0
    normal := v
    chart := G
    normalized := hv
    compact := hC
    convex := hcv
    center := hC0
    polyhedral := hpoly
    ball := ?_
    piecewiseAffine := hG
    link := ?_
    boundary := ?_ }⟩
  · rw [← hdualzero, hPb, hlinkbar]
    exact hball
  · intro x
    change (x : E) ∈ ((P.barycentricDualBlock {p}).link p).space ↔
      (H ⟨x, hsource.subset x.property⟩ : Fin 3 → ℝ) ∈ frontier C
    rw [hlinkspace]
    exact hlink ⟨x, hsource.subset x.property⟩
  · intro x
    change (H ⟨x, hsource.subset x.property⟩ : Fin 3 → ℝ) 0 = 0 ↔
      (x : E) ∈ (N.barycentricDualBlock {p}).space
    rw [← hdualzero]
    exact (hheight ⟨x, hsource.subset x.property⟩).trans (and_iff_right x.property).symm

end Geometry.SimplicialComplex
