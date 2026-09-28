import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcBranchLinks









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn


theorem exists_link_polygon_of_pair_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {q : E → ℝ × ℝ} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    {v : E} (hv : v ∈ K.vertices) (hint : q v ∈ interior (q '' K.space)) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (K.link v).space := by
  classical
  let L := hq.embeddedImage hi
  have hL : L.faces.Finite := hq.embeddedImage_finite hi hK
  have hvL : q v ∈ L.vertices := by
    rw [hq.embeddedImage_vertices hi]
    exact ⟨v, hv, rfl⟩
  have hintL : q v ∈ interior L.space := by
    rw [hq.embeddedImage_space hi]
    exact hint
  have hball := L.isFinitePLBallPair_closedStar_of_interior hL hvL hintL
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨n, P, hPi, hP, hPb⟩ := hball.exists_polygon_boundary
  let u := Function.invFunOn q K.space
  have hu : FinitePiecewiseAffineOn u L.space :=
    (hq.invFunOn_embeddedImage hi).finitePiecewiseAffineOn hL
  have hui : InjOn u L.space := by
    rw [hq.embeddedImage_space hi]
    exact Function.invFunOn_injOn_image q K.space
  have hsub : P.boundary ℝ ⊆ L.space := by
    rw [hPb]
    exact SimplicialComplex.space_subset_of_le
      (show L.link (q v) ≤ L from fun _ hs => hs.1)
  obtain ⟨m, Q, hQi, hQ, hQb⟩ :=
    P.exists_polygon_finitePL_image hP hPi hu hsub (hui.mono hsub)
  have hlink : (L.link (q v)).space = q '' (K.link v).space :=
    hq.embeddedImage_link_space hi hv
  have hlinksub : (K.link v).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (show K.link v ≤ K from fun _ hs => hs.1)
  refine ⟨m, Q, hQi, hQ, ?_⟩
  rw [hQb, hPb, hlink]
  exact hi.invFunOn_image hlinksub

theorem exists_link_polygon_of_planar_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {q : E → (Fin 2 → ℝ)} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    {v : E} (hv : v ∈ K.vertices) (hint : q v ∈ interior (q '' K.space)) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (K.link v).space := by
  let c := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  have hcq : K.AffineOnFaces (c ∘ q) := by
    intro face hface
    obtain ⟨a, ha⟩ := hq face hface
    exact ⟨c.toContinuousLinearMap.toContinuousAffineMap.comp a,
      fun x hx => congrArg c (ha hx)⟩
  have hci : InjOn (c ∘ q) K.space := c.injective.comp_injOn hi
  apply exists_link_polygon_of_pair_parameter K hK hcq hci hv
  have h := c.toHomeomorph.image_interior (q '' K.space)
  change c '' interior (q '' K.space) = interior (c '' (q '' K.space)) at h
  have hm := mem_image_of_mem c hint
  rw [h] at hm
  simpa only [image_image, Function.comp_def] using hm

end PoincareConjecture.M76.Dehn
