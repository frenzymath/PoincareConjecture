import PoincareConjecture.Proofs.M76.PrimeReduction.FiniteChartSurfaceImage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse



set_option autoImplicit false
open Set Geometry Module

namespace Geometry

theorem PolyhedralPLInCharts.exists_planar_chart_carrier
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (hdim : finrank ℝ E = 2)
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (Q : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (J : SimplicialComplex ℝ (Fin 3 → ℝ)) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) :
    ∃ P : SimplicialComplex ℝ (Fin 3 → ℝ), P.faces.Finite ∧
      P.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space ∧
      P.space ⊆ J.space ∧ (∀ a ∈ P.faces, a.card ≤ 3) ∧
      ∀ x ∈ J.space, Q.symm x ∈ f '' K.space ↔ x ∈ P.space := by
  have hcard (a : Finset E) (ha : a ∈ K.faces) : a.card ≤ 2 + 1 := by
    simpa only [Fintype.card_coe, hdim] using
      (K.indep ha).card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  obtain ⟨P, hP, hPs, hPc⟩ :=
    hf.exists_finite_chart_image_of_face_card_le K hK hcard Q hQ J hJ hJQ
  refine ⟨P, hP, hPs, fun x hx => (hPs.subset hx).2, hPc, ?_⟩
  intro x hx
  constructor
  · intro hxS
    exact hPs.symm.subset
      ⟨⟨Q.symm x, ⟨hxS, Q.map_target (hJQ hx)⟩, Q.right_inv (hJQ hx)⟩, hx⟩
  · intro hxP
    obtain ⟨⟨y, ⟨hyS, hyQ⟩, rfl⟩, _⟩ := hPs.subset hxP
    simpa only [Q.left_inv hyQ] using hyS

theorem PolyhedralPLInCharts.exists_clipped_source_parameter
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space) (hinj : InjOn f K.space)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (J P : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space) :
    ∃ g : F → E, FinitePiecewiseAffineOn g P.space ∧
      MapsTo g P.space K.space ∧ InjOn g P.space ∧
      (∀ w ∈ P.space, f (g w) = Q.symm w) ∧
      (∀ x ∈ K.space, f x ∈ Q.source → Q (f x) ∈ J.space → g (Q (f x)) = x) ∧
      g '' P.space = {x | x ∈ K.space ∧ f x ∈ Q.source ∧ Q (f x) ∈ J.space} := by
  obtain ⟨L, g, _, hLs, hg, hgK, hright, hleft⟩ :=
    hf.exists_finite_clipped_chart_inverse K hK hinj Q hQ J hJ hJQ
  have hLP : L.space = P.space := hLs.trans hPs.symm
  have hgP := hg.restrict P hP hLP.symm.subset
  have hcoord (w : F) (hw : w ∈ P.space) :
      f (g w) ∈ Q.source ∧ Q (f (g w)) = w := hright w (hLP.symm.subset hw)
  have hparam (w : F) (hw : w ∈ P.space) : f (g w) = Q.symm w := by
    exact (Q.left_inv (hcoord w hw).1).symm.trans
      (congrArg Q.symm (hcoord w hw).2)
  have hginj : InjOn g P.space := by
    intro a ha b hb hab
    exact ((hcoord a ha).2.symm.trans (congrArg (fun x => Q (f x)) hab)).trans
      (hcoord b hb).2
  refine ⟨g, hgP, fun w hw => hgK (hLP.symm.subset hw), hginj, hparam, hleft, ?_⟩
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hgK (hLP.symm.subset hw), (hcoord w hw).1,
      (hcoord w hw).2.symm ▸ (hPs.subset hw).2⟩
  · rintro ⟨hx, hsource, hwindow⟩
    exact ⟨Q (f x), hPs.symm.subset ⟨⟨f x, ⟨mem_image_of_mem f hx, hsource⟩, rfl⟩,
      hwindow⟩, hleft x hx hsource hwindow⟩

end Geometry
