import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarBoundaryExtension
import PoincareConjecture.Proofs.M76.Mathlib.SmallClosedStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarConvexFrontier
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
  {ι : Type*} [Finite ι] [Nonempty ι]

theorem isFinitePLBallPair_closedStar_zero_of_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hz : (0 : E) ∈ K.vertices) (hint : (0 : E) ∈ interior K.space)
    (c : E ≃L[ℝ] (ι → ℝ)) :
    IsFinitePLBallPair E (K.closedStar 0).space (K.link 0).space := by
  obtain ⟨C, L, _, hC, hcv, hC0, hCU, hdisj, hlocal, hL, hrep, _, _⟩ :=
    K.exists_small_closedStar_halfspace_neighborhood hK hz isOpen_interior hint c
  have hwhole : (K.closedStar 0).space ∩ frontier C = frontier C := by
    apply inter_eq_right.mpr
    intro x hx
    have hxC := hC.isClosed.frontier_subset hx
    exact (hlocal.subset ⟨interior_subset (hCU hxC), hxC⟩).1
  obtain ⟨e, he⟩ := K.exists_finitePL_link_convex_frontier_chart
    hK hC hcv hC0 hdisj L hL hrep
  let d := e.trans (Homeomorph.setCongr hwhole)
  have hd : d.IsFinitePL := he.setCongr rfl hwhole
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr
    ⟨⟨0, interior_subset hC0⟩, hC.ne_univ⟩
  have hne : (K.link 0).space.Nonempty := ⟨d.symm ⟨x, hx⟩, (d.symm ⟨x, hx⟩).property⟩
  exact hd.isFinitePLBallPair_closedStar K hK hz hne hC hcv hC0

theorem isFinitePLBallPair_closedStar_of_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) (hint : p ∈ interior K.space)
    (c : E ≃L[ℝ] (ι → ℝ)) :
    IsFinitePLBallPair E (K.closedStar p).space (K.link p).space := by
  classical
  let a : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hap : a p = 0 := by change -p + p = 0; exact neg_add_cancel p
  let hf := K.affineOnFaces_affine a.toContinuousAffineMap
  have hinj : InjOn (a.toContinuousAffineMap : E → E) K.space :=
    fun _ _ _ _ h => a.injective h
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hK
  have hJstar : (J.closedStar 0).space = a '' (K.closedStar p).space := by
    have h := hf.embeddedImage_closedStar_space hinj hp
    change (J.closedStar (a p)).space = a '' (K.closedStar p).space at h
    simpa only [hap] using h
  have hJlink : (J.link 0).space = a '' (K.link p).space := by
    have h := hf.embeddedImage_link_space hinj hp
    change (J.link (a p)).space = a '' (K.link p).space at h
    simpa only [hap] using h
  have hzJ : (0 : E) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices hinj]
    exact ⟨p, hp, hap⟩
  have hJint : (0 : E) ∈ interior J.space := by
    change (0 : E) ∈ interior (hf.embeddedImage hinj).space
    rw [hf.embeddedImage_space hinj]
    change (0 : E) ∈ interior (a.toHomeomorph '' K.space)
    rw [← a.toHomeomorph.image_interior]
    exact ⟨p, hint, hap⟩
  have hball := J.isFinitePLBallPair_closedStar_zero_of_interior hJ hzJ hJint c
  have hback (S : Set E) : a.symm '' (a '' S) = S := by simp
  have himage := hball.affine_image a.symm.toContinuousAffineMap a.symm.injective.injOn
  change IsFinitePLBallPair E
    (a.symm '' (J.closedStar 0).space) (a.symm '' (J.link 0).space) at himage
  simpa only [hJstar, hJlink, hback] using himage

end Geometry.SimplicialComplex
