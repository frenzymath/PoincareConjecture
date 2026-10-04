import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.StandardTriangleDiskChart
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonFinitePLTriangleFilling
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineInnermostDisk

/-!
# Standard finite PL charts of affine polygon disks

Invert the affine inclusion, use the actual polygon triangle
filling and include the target triangle in its attachment plane.
The entire boundary and innermost incidence are retained. See
Alexander 1924, pp. 6--7, Hudson 1969, pp. 15--19 and derivation 130.
-/

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An affinely embedded polygon disk has an actual finite PL
chart to the standard attachment disk identifying its complete
boundary with the rim. See M76 derivation 130. -/
theorem exists_affine_disk_chart {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (a : (ℝ × ℝ) →ᴬ[ℝ] E) (ha : Function.Injective a) :
    ∃ e : (a '' closure P.inside) ≃ₜ disk, e.IsFinitePL ∧
      ∀ x : a '' closure P.inside,
        (x : E) ∈ a '' P.boundary ℝ ↔ (e x : (ℝ × ℝ) × ℝ) ∈ rim := by
  obtain ⟨f, hf, hfb, _⟩ := P.exists_finitePL_triangle_filling hP hinj
    (P.isFinitePLBallPair_closed_inside hP hinj)
    TriangleDiskModel.rightTriangle TriangleDiskModel.independent_rightTriangle
  have hcopy := hf
  obtain ⟨_, ⟨K, hK, hspace, _⟩, _⟩ := hcopy
  have haPL : FinitePiecewiseAffineOn a (closure P.inside) :=
    ⟨K, hK, hspace, K.affineOnFaces_affine a⟩
  obtain ⟨ea, hea, hval⟩ := haPL.exists_homeomorph_image ha.injOn
  obtain ⟨g, hg, hgb⟩ := exists_triangle_disk_chart
  let e := ea.symm.trans (f.trans g)
  refine ⟨e, hea.symm.trans (hf.trans hg), fun x => ?_⟩
  have hx : a (ea.symm x) = (x : E) := by rw [← hval, ea.apply_symm_apply]
  have hmem : (x : E) ∈ a '' P.boundary ℝ ↔ (ea.symm x : ℝ × ℝ) ∈ P.boundary ℝ := by
    rw [← hx]
    exact ha.mem_set_image
  exact hmem.trans ((hfb (ea.symm x)).trans (hgb (f (ea.symm x))))

/-- An innermost affine section disk admits a standard finite
PL attachment chart without losing its exact surface incidence.
See Alexander p. 7 and M76 derivation 130. -/
theorem exists_innermost_affine_disk_chart {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (hdisj : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    (a : (ℝ × ℝ) →ᴬ[ℝ] E) (ha : Function.Injective a) (S : Set E)
    (hsection : a ⁻¹' S = ⋃ i, (P i).boundary ℝ) :
    ∃ (i : ι) (e : (a '' closure (P i).inside) ≃ₜ disk), e.IsFinitePL ∧
      (∀ x : a '' closure (P i).inside,
        (x : E) ∈ a '' (P i).boundary ℝ ↔ (e x : (ℝ × ℝ) × ℝ) ∈ rim) ∧
      (a '' closure (P i).inside) ∩ S = a '' (P i).boundary ℝ ∧
      Disjoint (a '' (P i).inside) S := by
  obtain ⟨i, _, hinter, hdis⟩ := exists_innermost_affine_disk n P hP hinj hdisj a ha S hsection
  obtain ⟨e, he, hb⟩ := (P i).exists_affine_disk_chart (hP i) (hinj i) a ha
  exact ⟨i, e, he, hb, hinter, hdis⟩

end Polygon
