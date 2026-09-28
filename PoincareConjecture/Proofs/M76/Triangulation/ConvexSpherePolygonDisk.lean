import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereLargeDisks
import PoincareConjecture.Proofs.M76.Mathlib.PolygonPLSubdisk
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_convex_sphere_polygon_disk_with_interior (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = 3) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ frontier s) (p : frontier s)
    (hp : (p : E) ∉ P.boundary ℝ) :
    ∃ D : Set E, IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧
      D ⊆ frontier s ∧ (p : E) ∉ D ∧
      interior ((Subtype.val : frontier s → E) ⁻¹' D) =
        (Subtype.val : frontier s → E) ⁻¹' (D \ P.boundary ℝ) := by
  obtain ⟨d, q, hd, hds, hPd, hpd, hopen⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK hs hcv
      hne hspace (F := ℝ × ℝ) (by simpa [Module.finrank_prod] using hdim)
      p P.isCompact_boundary hPsub hp
  obtain ⟨D, hD, hDd, hint⟩ := hd.exists_polygon_subdisk_with_interior P hP hinj hPd
  refine ⟨D, hD, hDd.trans (sdiff_subset.trans hds), fun hx => hpd (hDd hx).1, ?_⟩
  exact interior_preimage_val_of_open_neighborhood hds (hDd.trans sdiff_subset)
    sdiff_subset hopen (sdiff_subset.trans hDd) sdiff_subset hint





theorem exists_convex_sphere_polygon_disk (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = 3) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ frontier s) (p : frontier s)
    (hp : (p : E) ∉ P.boundary ℝ) :
    ∃ D : Set E, IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧
      D ⊆ frontier s ∧ (p : E) ∉ D := by
  obtain ⟨D, hD, hDs, hpD, _⟩ := K.exists_convex_sphere_polygon_disk_with_interior
    hK hs hcv hne hspace hdim P hP hinj hPsub p hp
  exact ⟨D, hD, hDs, hpD⟩

end Geometry.SimplicialComplex
