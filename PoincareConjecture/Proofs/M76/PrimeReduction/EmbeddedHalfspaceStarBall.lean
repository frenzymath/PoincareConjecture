import PoincareConjecture.Proofs.M76.PrimeReduction.HalfspaceStarBall
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [DecidableEq E]
  {ι : Type*} [Finite ι] [Nonempty ι]

theorem AffineOnFaces.exists_halfspace_star_ball
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite)
    {f : E → F} (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    {p : E} (hp : p ∈ K.vertices) (hfp : f p = 0)
    (hself : (K.closedStar p).space = K.space)
    (A : F →ₗ[ℝ] ℝ) (v : F) (hv : 0 < A v)
    (hside : f '' K.space ⊆ {x | 0 ≤ A x})
    {U : Set F} (hU : IsOpen U) (h0U : (0 : F) ∈ U)
    (hhalf : U ∩ {x | 0 ≤ A x} ⊆ f '' K.space)
    (c : F ≃L[ℝ] (ι → ℝ)) :
    ∃ (C : Set F) (H : K.space ≃ₜ (C ∩ {x | 0 ≤ A x} : Set F)),
      IsCompact C ∧ Convex ℝ C ∧ (0 : F) ∈ interior C ∧
      (∃ J : SimplicialComplex ℝ F, J.faces.Finite ∧ J.space = C) ∧
      IsFinitePLBallPair F K.space
        ((K.link p).space ∪ (K.space ∩ {x | A (f x) = 0})) ∧
      H.IsFinitePL ∧
      (∀ x : K.space, (x : E) ∈ (K.link p).space ↔ (H x : F) ∈ frontier C) ∧
      ∀ x : K.space, A (H x : F) = 0 ↔ A (f x) = 0 := by
  classical
  let J := hf.embeddedImage hinj
  have hJ := hf.embeddedImage_finite hinj hK
  have hJs : J.space = f '' K.space := hf.embeddedImage_space hinj
  have hJp : (0 : F) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices hinj]
    exact ⟨p, hp, hfp⟩
  have hJstar : (J.closedStar 0).space = J.space := by
    have h := hf.embeddedImage_closedStar_space hinj hp
    change (J.closedStar (f p)).space = f '' (K.closedStar p).space at h
    simpa only [hfp, hself, ← hJs] using h
  have hJlink : (J.link 0).space = f '' (K.link p).space := by
    have h := hf.embeddedImage_link_space hinj hp
    change (J.link (f p)).space = f '' (K.link p).space at h
    simpa only [hfp] using h
  obtain ⟨C, H, hC, hcv, hC0, hpoly, hpair, hH, hboundary, hzero⟩ :=
    J.exists_finitePL_closedStar_half_body hJ hJp A v hv
      (hJs.subset.trans hside) hU h0U (hhalf.trans hJs.symm.subset) c
  let e := hf.embeddedHomeomorph hinj hK
  have he : e.IsFinitePL := ⟨f, ⟨K, hK, rfl, hf⟩, fun _ => rfl⟩
  let d := e.trans (Homeomorph.setCongr hJstar.symm)
  have hd : d.IsFinitePL := he.setCongr rfl hJstar.symm
  have hlinkK : (K.link p).space ⊆ K.space :=
    (space_subset_of_le (K.link_le_closedStar p)).trans hself.subset
  have hlink (x : K.space) : (x : E) ∈ (K.link p).space ↔
      (d x : F) ∈ (J.link 0).space := by
    change (x : E) ∈ (K.link p).space ↔ f x ∈ (J.link 0).space
    rw [hJlink]
    constructor
    · exact fun hx => mem_image_of_mem f hx
    · rintro ⟨y, hy, heq⟩
      exact hinj (hlinkK hy) x.property heq ▸ hy
  have hpairK : IsFinitePLBallPair F K.space
      ((K.link p).space ∪ (K.space ∩ {x | A (f x) = 0})) := by
    apply hpair.of_homeomorph (union_subset hlinkK inter_subset_left) d hd
    intro x
    change ((x : E) ∈ (K.link p).space ∨
      (x : E) ∈ K.space ∧ A (f x) = 0) ↔
      (d x : F) ∈ (J.link 0).space ∨
        (d x : F) ∈ (J.closedStar 0).space ∧ A (d x : F) = 0
    simp only [x.property, (d x).property, true_and]
    exact or_congr (hlink x) Iff.rfl
  exact ⟨C, d.trans H, hC, hcv, hC0, hpoly, hpairK, hd.trans hH,
    fun x => (hlink x).trans (hboundary (d x)), fun x => hzero (d x)⟩

end Geometry.SimplicialComplex
