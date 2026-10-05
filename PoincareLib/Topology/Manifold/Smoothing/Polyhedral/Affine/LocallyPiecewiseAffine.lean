import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralRefinement
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.AffineSubdivisionComposition

/-!+# Locally piecewise-affine coordinate maps

Finite polyhedral neighborhoods define the local PL property
independently of a chosen triangulation. Common refinements and
map-aligned subdivisions prove restriction and composition.
See Hudson 1969, pp. 5, 12--19, Hamilton 1976, pp. 64, 68--69
and M76 derivation 80.
-/

set_option autoImplicit false

open Set Topology

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A map is locally piecewise affine on a set if every point has
a finite polyhedral neighborhood inside that set on whose faces
the map is affine. See Hudson pp. 5, 15--19 and M76 derivation 80. -/
def LocallyPiecewiseAffineOn (f : E → F) (U : Set E) : Prop :=
  ∀ x ∈ U, ∃ K : SimplicialComplex ℝ E,
    K.faces.Finite ∧ x ∈ interior K.space ∧ K.space ⊆ U ∧ K.AffineOnFaces f

variable {f g : E → F} {U V : Set E}

/-- The local polyhedral neighborhood condition forces an open
source. See Hudson p. 5 and M76 derivation 80. -/
theorem LocallyPiecewiseAffineOn.isOpen (hf : LocallyPiecewiseAffineOn f U) : IsOpen U := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨K, _, hxK, hKU, _⟩ := hf x hx
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hxK) hKU

/-- A locally piecewise-affine map is continuous on its source.
See Hudson pp. 15--17 and M76 derivation 80. -/
theorem LocallyPiecewiseAffineOn.continuousOn (hf : LocallyPiecewiseAffineOn f U) :
    ContinuousOn f U := by
  intro x hx
  obtain ⟨K, hK, hxK, _, hfK⟩ := hf x hx
  exact ((hfK.continuousOn hK).continuousAt
    (mem_interior_iff_mem_nhds.mp hxK)).continuousWithinAt

/-- Local piecewise-affineness depends only on values in its
source. See Hudson pp. 15--17 and M76 derivation 80. -/
theorem LocallyPiecewiseAffineOn.congr (hf : LocallyPiecewiseAffineOn f U)
    (hfg : EqOn f g U) : LocallyPiecewiseAffineOn g U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  exact ⟨K, hK, hxK, hKU, hfK.congr (hfg.mono hKU)⟩

/-- The local property assembles from a covering of local source
patches. See Hamilton p. 69 and M76 derivation 80. -/
theorem LocallyPiecewiseAffineOn.locality
    (hf : ∀ x ∈ U, ∃ V : Set E, x ∈ V ∧ LocallyPiecewiseAffineOn f (U ∩ V)) :
    LocallyPiecewiseAffineOn f U := by
  intro x hx
  obtain ⟨V, hxV, hV⟩ := hf x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hV x ⟨hx, hxV⟩
  exact ⟨K, hK, hxK, fun _ hy => (hKU hy).1, hfK⟩

variable [FiniteDimensional ℝ E]

/-- Local piecewise-affineness restricts to any open subset of
its source. See Hudson pp. 12--17 and M76 derivation 80. -/
theorem LocallyPiecewiseAffineOn.mono (hf : LocallyPiecewiseAffineOn f U)
    (hV : IsOpen V) (hVU : V ⊆ U) : LocallyPiecewiseAffineOn f V := by
  intro x hx
  obtain ⟨K, hK, hxK, _, hfK⟩ := hf x (hVU hx)
  obtain ⟨R, hR, hxR, hRV, hfR⟩ := hfK.exists_finite_neighborhood hK
    isCompact_singleton hV (singleton_subset_iff.mpr ⟨hxK, hx⟩)
  exact ⟨R, hR, hxR (mem_singleton x), fun _ hy => (hRV hy).2, hfR⟩

/-- Affine maps have local finite simplicial formulas on every
open source. See Hudson p. 15 and M76 derivation 80. -/
theorem locallyPiecewiseAffineOn_affine (a : E →ᴬ[ℝ] F) (hU : IsOpen U) :
    LocallyPiecewiseAffineOn a U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    isCompact_singleton hU (singleton_subset_iff.mpr hx)
  exact ⟨K, hK, hxK (mem_singleton x), hKU, K.affineOnFaces_affine a⟩

variable [FiniteDimensional ℝ F]

/-- Local piecewise-affine maps compose on the appropriate
source intersection. A local subdivision aligns their affine
formulas. See Hudson pp. 15--17 and M76 derivation 80. -/
theorem LocallyPiecewiseAffineOn.comp {g : F → G} {V : Set F}
    (hg : LocallyPiecewiseAffineOn g V) (hf : LocallyPiecewiseAffineOn f U) :
    LocallyPiecewiseAffineOn (g ∘ f) (U ∩ f ⁻¹' V) := by
  classical
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx.1
  obtain ⟨L, hL, hfxL, hLV, hgL⟩ := hg (f x) hx.2
  have hO : IsOpen (interior K.space ∩ f ⁻¹' interior L.space) :=
    ((hfK.continuousOn hK).mono interior_subset).isOpen_inter_preimage
      isOpen_interior isOpen_interior
  obtain ⟨R, hR, hxR, hRO, hfR⟩ := hfK.exists_finite_neighborhood hK
    isCompact_singleton hO (singleton_subset_iff.mpr ⟨hxK, hxK, hfxL⟩)
  let N := hR.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ R.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hR.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨T, hT, hTR, _, hcomp⟩ := hfR.exists_subdivision_comp hgL hR hL
    (fun _ hy => interior_subset (hRO hy).2.2) hN
  refine ⟨T, hT, ?_, ?_, hcomp⟩
  · rw [hTR.space_eq]
    exact hxR (mem_singleton x)
  · intro y hy
    have hyR : y ∈ R.space := hTR.space_eq ▸ hy
    exact ⟨hKU (interior_subset (hRO hyR).1),
      hLV (interior_subset (hRO hyR).2.2)⟩

end Geometry
