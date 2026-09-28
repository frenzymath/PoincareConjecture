import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartImageIntersection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages












set_option autoImplicit false

open Set

namespace Geometry





theorem PolyhedralPLInCharts.exists_finite_clipped_chart_inverse
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space) (hinj : InjOn f K.space)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target) :
    ∃ (L : SimplicialComplex ℝ F) (g : F → E), L.faces.Finite ∧
      L.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space ∧
      FinitePiecewiseAffineOn g L.space ∧ MapsTo g L.space K.space ∧
      (∀ w ∈ L.space, f (g w) ∈ Q.source ∧ Q (f (g w)) = w) ∧
      ∀ x ∈ K.space, f x ∈ Q.source → Q (f x) ∈ J.space → g (Q (f x)) = x := by
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let A : Set K.space := (fun x => f x) ⁻¹' (Q.symm '' J.space)
  let O : Set K.space := (fun x => f x) ⁻¹' Q.source
  have hcompact : IsCompact (Q.symm '' J.space) :=
    (J.isCompact_space_of_finite hJ).image_of_continuousOn
      (Q.symm.continuousOn.mono hJQ)
  have hA : IsCompact A :=
    (hcompact.isClosed.preimage hf.continuousOn.domRestrict).isCompact
  have hO : IsOpen O := Q.open_source.preimage hf.continuousOn.domRestrict
  have hAO : A ⊆ O := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hx
    change Q.symm y = f x at heq
    change f x ∈ Q.source
    rw [← heq]
    exact Q.map_target (hJQ hy)
  obtain ⟨N, V, hN, hNK, _, hAV, hVN, hNO⟩ :=
    K.exists_relative_compact_polyhedral_neighborhood hK hA hO hAO
  have hNQ : MapsTo f N.space Q.source := by
    intro x hx
    exact hNO (show (⟨x, hNK hx⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hx)
  have hsource {x : E} (hx : x ∈ K.space) (hfx : f x ∈ Q.source)
      (hcoord : Q (f x) ∈ J.space) : x ∈ N.space := by
    have hxA : (⟨x, hx⟩ : K.space) ∈ A := ⟨Q (f x), hcoord, Q.left_inv hfx⟩
    exact hVN (mem_image_of_mem Subtype.val (hAV hxA))
  have hfN := hf.restrict_finite N hN hNK
  have hcoords := hfN.finitePiecewiseAffineOn_compatible_chart_finite_source N hN Q hQ hNQ
  have hcoordsinj : InjOn (Q ∘ f) N.space := by
    intro x hx y hy heq
    exact hinj (hNK hx) (hNK hy) (Q.injOn (hNQ hx) (hNQ hy) heq)
  obtain ⟨H, hH, hHval⟩ := hcoords.exists_homeomorph_image hcoordsinj
  obtain ⟨g, hg, hgval⟩ := hH.symm
  have hleft {x : E} (hx : x ∈ N.space) : g (Q (f x)) = x := by
    have h := hgval (H ⟨x, hx⟩)
    rw [H.symm_apply_apply] at h
    change x = g ((H ⟨x, hx⟩ : F)) at h
    rw [hHval] at h
    exact h.symm
  obtain ⟨L, hL, hLs⟩ := hf.exists_finite_chart_image_intersection K hK Q hQ J hJ hJQ
  have hsub : L.space ⊆ (Q ∘ f) '' N.space := by
    intro w hw
    rw [hLs] at hw
    obtain ⟨⟨y, ⟨⟨x, hx, rfl⟩, hfx⟩, rfl⟩, hcoord⟩ := hw
    exact ⟨x, hsource hx hfx hcoord, rfl⟩
  refine ⟨L, g, hL, hLs, hg.restrict L hL hsub, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := hsub hw
    change g (Q (f x)) ∈ K.space
    rw [hleft hx]
    exact hNK hx
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := hsub hw
    change f (g (Q (f x))) ∈ Q.source ∧ Q (f (g (Q (f x)))) = Q (f x)
    rw [hleft hx]
    exact ⟨hNQ hx, rfl⟩
  · intro x hx hfx hcoord
    exact hleft (hsource hx hfx hcoord)

end Geometry
