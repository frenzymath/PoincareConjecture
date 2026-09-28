import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGluing










set_option autoImplicit false

open Set

namespace Geometry

variable {E V M ι σ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [Finite σ]
  {e : ι → OpenPartialHomeomorph M V}




theorem polyhedralPLInCharts_of_finite_cover
    (hcover_e : ∀ x : M, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : σ → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    {f : E → M} (hf : ContinuousOn f K.space)
    (hPL : ∀ i, PolyhedralPLInCharts e f (J i).space)
    (hcover : K.space ⊆ ⋃ i, (J i).space) :
    PolyhedralPLInCharts e f K.space := by
  classical
  refine ⟨hf, ?_⟩
  intro x
  obtain ⟨j, hxj⟩ := hcover_e (f x)
  let O : Set K.space := (fun y => f y) ⁻¹' (e j).source
  have hO : IsOpen O := (e j).open_source.preimage hf.domRestrict
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hxj
  have hNj : MapsTo f N.space (e j).source := by
    intro y hy
    exact hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)
  have hpieces (i : σ) : ∃ C : SimplicialComplex ℝ E,
      C.faces.Finite ∧ C.space = N.space ∩ (J i).space ∧
      C.AffineOnFaces ((e j) ∘ f) := by
    obtain ⟨L, hL, hLspace⟩ := N.exists_finite_triangulation_inter (J i) hN (hJ i)
    have hLN : L.space ⊆ N.space := fun y hy => (hLspace.subset hy).1
    have hLJ : L.space ⊆ (J i).space := fun y hy => (hLspace.subset hy).2
    have hfL := (hPL i).restrict_finite L hL hLJ
    have hcoords := hfL.finitePiecewiseAffineOn_fixed_chart hcompat L hL j
      (fun y hy => hNj (hLN hy))
    obtain ⟨C, hC, hCL, hFC⟩ := hcoords
    exact ⟨C, hC, hCL.trans hLspace, hFC⟩
  choose C hC hCspace hFC using hpieces
  have hcoverN : N.space ⊆ ⋃ i, (C i).space := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (hNK hy))
    exact mem_iUnion.mpr ⟨i, (hCspace i).symm.subset ⟨hy, hi⟩⟩
  exact ⟨j, N, W, hN, hNK, hW, hxW, hWN, hNj,
    finitePiecewiseAffineOn_of_finite_cover N hN C hC hFC hcoverN⟩

end Geometry
