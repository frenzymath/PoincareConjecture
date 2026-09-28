import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualEdgeDisk










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]




theorem isFinitePLBallPair_dualBlock_of_polygon_faceLink
    {s : Finset E} (hs : s ∈ K.faces) {n : ℕ} (P : Polygon E (n + 3))
    (hPi : Function.Injective P) (hP : P.HasSimplicialEdges)
    (hPs : P.boundary ℝ = (K.faceLink s).space) :
    IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock s).space
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  obtain ⟨_, e, ⟨g, hg, heg⟩, _, _⟩ := K.exists_finitePL_barycentricDualLink hs
  have hginj : InjOn g (K.faceLink s).space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [heg] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  have hgs : g '' (K.faceLink s).space =
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← heg ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← heg, e.apply_symm_apply]
  obtain ⟨m, Q, hQi, hQ, hQb⟩ := P.exists_polygon_finitePL_image hP hPi hg
    hPs.subset (hginj.mono hPs.subset)
  have hQs : Q.boundary ℝ =
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
    rw [hQb, hPs, hgs]
  have hball := (K.barycentricDualBlock s).isFinitePLBallPair_closedStar_of_polygon_link
    (K.barycentricDualBlock_finite s) (K.faceCentroid_mem_barycentricDualBlock_vertices hs)
    Q hQ hQi hQs
  simpa only [K.barycentricDualBlock_closedStar_faceCentroid hs] using hball

end Geometry.SimplicialComplex
