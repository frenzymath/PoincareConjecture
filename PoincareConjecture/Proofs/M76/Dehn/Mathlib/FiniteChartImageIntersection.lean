import PoincareConjecture.Proofs.M76.Dehn.Mathlib.RelativeCompactPolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections

set_option autoImplicit false

open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_finite_chart_image_intersection
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) :
    ∃ L : SimplicialComplex ℝ F, L.faces.Finite ∧
      L.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (K.isCompact_space_of_finite hK)
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
  have hfN := hf.restrict_finite N hN hNK
  have hcoords := hfN.finitePiecewiseAffineOn_compatible_chart_finite_source N hN Q hQ hNQ
  obtain ⟨B, hB, hBs⟩ := hcoords.exists_finite_triangulation_image
  obtain ⟨L, hL, hLs⟩ := B.exists_finite_triangulation_inter J hB hJ
  refine ⟨L, hL, hLs.trans ?_⟩
  rw [hBs]
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨⟨f x, ⟨mem_image_of_mem f (hNK hx), hNQ hx⟩, rfl⟩, hz⟩
  · rintro ⟨⟨y, ⟨⟨x, hx, rfl⟩, hfx⟩, rfl⟩, hz⟩
    have hxA : (⟨x, hx⟩ : K.space) ∈ A :=
      ⟨Q (f x), hz, Q.left_inv hfx⟩
    have hxN : x ∈ N.space :=
      hVN (mem_image_of_mem Subtype.val (hAV hxA))
    exact ⟨⟨x, hxN, rfl⟩, hz⟩

end Geometry
