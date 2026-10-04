import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.CompactLocallyPLComposition
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.RelativePolyhedralNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.FinitePLCoordinates
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# PL maps from closed polyhedral sources into actual charts

The source neighborhoods are taken in the original carrier
topology. Their finite polyhedral patches retain complete
coordinate formulas and original chart-domain bounds. Local
PL functions on the target compose with these maps, and the
retained affine projections of a graph model transfer finite
PL maps back to the actual atlas. See Hudson 1969, pp. 15--19,
Hatcher's 3-manifold notes, Theorem 3.1, p. 45 and derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M]

/-- Local finite polyhedral source patches give actual PL
coordinate formulas in a specified target atlas. All source
neighborhoods use the relative topology of the original set,
which may include boundary points and need not be open.
See Hudson pp. 15--19 and M76 derivation 270. -/
structure PolyhedralPLInCharts (e : ι → OpenPartialHomeomorph M F)
    (f : E → M) (S : Set E) : Prop where
  continuousOn : ContinuousOn f S
  coordinates : ∀ x : S,
    ∃ (i : ι) (J : SimplicialComplex ℝ E) (V : Set S),
      J.faces.Finite ∧ J.space ⊆ S ∧ IsOpen V ∧ x ∈ V ∧
      Subtype.val '' V ⊆ J.space ∧ MapsTo f J.space (e i).source ∧
      FinitePiecewiseAffineOn ((e i) ∘ f) J.space

/-- A function locally PL in all target charts composes with
a chartwise PL map from a finite closed source polyhedron.
The result has one finite PL formula on the complete original
source carrier. See Hudson pp. 15--19 and derivation 270. -/
theorem PolyhedralPLInCharts.finitePiecewiseAffineOn_comp
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph M F} {f : E → M}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space) {g : M → G}
    (hg : ∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) :
    FinitePiecewiseAffineOn (g ∘ f) K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, J, V, _, _, hV, hxV, hVJ, hfJ, hcoords⟩ := hf.coordinates x
  have hcomp : FinitePiecewiseAffineOn ((g ∘ (e i).symm) ∘ ((e i) ∘ f)) J.space :=
    (hg i).comp_finitePiecewiseAffineOn hcoords (fun y hy => (e i).mapsTo (hfJ hy))
  have hgf : FinitePiecewiseAffineOn (g ∘ f) J.space := hcomp.congr (by
    intro y hy
    exact congrArg g ((e i).left_inv (hfJ hy)))
  obtain ⟨L, hL, hLs, hgfL⟩ := hgf
  refine ⟨L, V, hL, hV, hxV, ?_, hgfL⟩
  intro y hy
  exact hLs.symm.subset (hVJ hy)

/-- Original atlas coordinates recovered by fixed ambient
affine projections make a transported finite PL map chartwise
PL on its entire closed source. Only the retained projection
identities on actual open target neighborhoods are used.
See Hamilton 1976, p. 69, Hudson pp. 15--19 and derivation 270. -/
theorem polyhedralPLInCharts_of_affine_projections
    [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M F) (Fmap : M → G) (C : Set M)
    (hcharts : ∀ y ∈ C, ∃ (i : ι) (W : Set M) (a : G →ᴬ[ℝ] F),
      IsOpen W ∧ y ∈ W ∧ W ⊆ (e i).source ∧ EqOn (a ∘ Fmap) (e i) W)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → M} {g : E → G} (hf : ContinuousOn f K.space)
    (hfC : MapsTo f K.space C) (hg : FinitePiecewiseAffineOn g K.space)
    (hFg : EqOn (Fmap ∘ f) g K.space) : PolyhedralPLInCharts e f K.space := by
  refine ⟨hf, ?_⟩
  intro x
  obtain ⟨i, W, a, hW, hxW, hWe, hproj⟩ := hcharts (f x) (hfC x.property)
  let O : Set K.space := (fun y => f y) ⁻¹' W
  have hO : IsOpen O := hW.preimage
    (hf.comp_continuous continuous_subtype_val (fun y => y.property))
  obtain ⟨J, V, hJ, hJK, hV, hxV, hVJ, hJO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hxW
  have hJW (y : E) (hy : y ∈ J.space) : f y ∈ W :=
    hJO (show (⟨y, hJK hy⟩ : K.space) ∈ Subtype.val ⁻¹' J.space from hy)
  refine ⟨i, J, V, hJ, hJK, hV, hxV, hVJ, fun y hy => hWe (hJW y hy), ?_⟩
  apply ((hg.postcomp a).restrict J hJ hJK).congr
  intro y hy
  change a (g y) = e i (f y)
  rw [← hFg (hJK hy)]
  exact hproj (hJW y hy)

end Geometry
