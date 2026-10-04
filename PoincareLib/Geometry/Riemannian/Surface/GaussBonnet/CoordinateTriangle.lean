import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Triangle
import PoincareLib.Topology.Surface.Triangulation.Edges.CollarCoordinates
import PoincareLib.Topology.Plane.Triangles.Right
import PoincareLib.Topology.Plane.Meshes.Subdivision.Lines

/-!
# Standard coordinates for smooth affine triangle faces

The coordinate faces used by the surface subdivision have arbitrary affine
vertices. An explicit affine change of variables gives the standard triangle
chart required by the local Gauss--Bonnet formula, retaining all three sides.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff
open Poincare.Topology.Plane.Triangles Poincare.Topology.Plane.Meshes

namespace PoincareMT.Topology.Surface

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

private noncomputable def unitTriangleBasis : AffineBasis (Fin 3) ℝ E2 :=
  rightTriangleBasis (show (0 : ℝ) < 1 by norm_num)

/-- The ordered vertices of the standard triangle in product coordinates. -/
def standardTriangleVertex : Fin 3 → ℝ × ℝ := ![(0, 0), (1, 0), (0, 1)]

/-- The affine parametrization carrying the standard triangle to an arbitrary
ordered nondegenerate coordinate triangle. -/
noncomputable def triangleParameterEquiv (b : AffineBasis (Fin 3) ℝ E2) :
    (ℝ × ℝ) ≃ᴬ[ℝ] E2 :=
  collarParameterEquiv.symm.toContinuousAffineEquiv.trans
    (AffineEquiv.toContinuousAffineEquiv
      (triangleAffineEquiv unitTriangleBasis b unitTriangleBasis.ind b.ind))

private theorem triangleParameterEquiv_apply (b : AffineBasis (Fin 3) ℝ E2) (p : ℝ × ℝ) :
    triangleParameterEquiv b p =
      triangleAffineEquiv unitTriangleBasis b unitTriangleBasis.ind b.ind
        (collarParameterEquiv.symm p) := rfl

theorem triangleParameterEquiv_vertex (b : AffineBasis (Fin 3) ℝ E2) (i : Fin 3) :
    triangleParameterEquiv b (standardTriangleVertex i) = b i := by
  have hv : collarParameterEquiv.symm (standardTriangleVertex i) =
      unitTriangleBasis i := by
    apply collarParameterEquiv.injective
    rw [collarParameterEquiv.apply_symm_apply]
    fin_cases i <;> rfl
  rw [triangleParameterEquiv_apply, hv, triangleAffineEquiv_apply]

theorem triangleParameterEquiv_side (b : AffineBasis (Fin 3) ℝ E2)
    (i j : Fin 3) (t : ℝ) :
    triangleParameterEquiv b
        (AffineMap.lineMap (standardTriangleVertex i) (standardTriangleVertex j) t) =
      AffineMap.lineMap (b i) (b j) t := by
  have h := AffineMap.apply_lineMap (triangleParameterEquiv b).toAffineEquiv.toAffineMap
    (standardTriangleVertex i) (standardTriangleVertex j) t
  change triangleParameterEquiv b _ = AffineMap.lineMap
    (triangleParameterEquiv b (standardTriangleVertex i))
    (triangleParameterEquiv b (standardTriangleVertex j)) t at h
  simpa only [triangleParameterEquiv_vertex] using h

theorem triangleParameterEquiv_image (b : AffineBasis (Fin 3) ℝ E2) :
    triangleParameterEquiv b ''
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} =
      convexHull ℝ (range b) := by
  have hstandard : collarParameterEquiv.symm ''
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} =
      convexHull ℝ (range (rightTriangleBasis (show (0 : ℝ) < 1 by norm_num))) := by
    rw [rightTriangleBasis_convexHull]
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hz
      exact ⟨collarParameterEquiv z, hz, collarParameterEquiv.symm_apply_apply z⟩
  change (triangleAffineEquiv unitTriangleBasis b unitTriangleBasis.ind b.ind ∘
    collarParameterEquiv.symm) '' _ = _
  simp only [Function.comp_def]
  rw [← image_image (triangleAffineEquiv unitTriangleBasis b unitTriangleBasis.ind b.ind)
    collarParameterEquiv.symm, hstandard]
  exact triangleAffineEquiv_image_convexHull unitTriangleBasis b unitTriangleBasis.ind b.ind

variable {S : Type*} [TopologicalSpace S]

/-- The normalized chart of a smooth coordinate triangle. -/
noncomputable def coordinateTriangleChart (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2) : OpenPartialHomeomorph S (ℝ × ℝ) :=
  ((triangleParameterEquiv b).toHomeomorph.toOpenPartialHomeomorph.trans F).symm

theorem coordinateTriangleChart_source (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2) :
    (coordinateTriangleChart F b).source = F.target := by
  ext x
  change (x ∈ F.target ∧ F.symm x ∈ univ) ↔ x ∈ F.target
  simp

theorem coordinateTriangleChart_smooth [ChartedSpace E2 S] (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞
      (coordinateTriangleChart F b) (coordinateTriangleChart F b).source := by
  exact (triangleParameterEquiv b).symm.toContinuousAffineMap.contDiff.contMDiff.comp_contMDiffOn
    (hF.mono (fun _ hx => hx.1))

theorem coordinateTriangleChart_smooth_symm [ChartedSpace E2 S]
    (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (coordinateTriangleChart F b).symm (coordinateTriangleChart F b).target := by
  exact hF.comp
    (triangleParameterEquiv b).toContinuousAffineMap.contDiff.contMDiff.contMDiffOn
    (fun _ hx => hx.2)

theorem coordinateTriangleChart_target (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2) (hsource : convexHull ℝ (range b) ⊆ F.source) :
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆
      (coordinateTriangleChart F b).target := by
  intro p hp
  exact ⟨mem_univ _, hsource (triangleParameterEquiv_image b ▸ mem_image_of_mem _ hp)⟩

theorem coordinateTriangleChart_image (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2) :
    (coordinateTriangleChart F b).symm ''
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} =
      F '' convexHull ℝ (range b) := by
  change (F ∘ triangleParameterEquiv b) '' _ = _
  simp only [Function.comp_def]
  rw [← image_image F (triangleParameterEquiv b), triangleParameterEquiv_image]

theorem coordinateTriangleChart_vertex (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2) (i : Fin 3) :
    (coordinateTriangleChart F b).symm (standardTriangleVertex i) = F (b i) := by
  change F (triangleParameterEquiv b (standardTriangleVertex i)) = _
  rw [triangleParameterEquiv_vertex]

theorem coordinateTriangleChart_side (F : OpenPartialHomeomorph E2 S)
    (b : AffineBasis (Fin 3) ℝ E2) (i j : Fin 3) (t : ℝ) :
    (coordinateTriangleChart F b).symm
        (AffineMap.lineMap (standardTriangleVertex i) (standardTriangleVertex j) t) =
      F (AffineMap.lineMap (b i) (b j) t) := by
  change F (triangleParameterEquiv b _) = _
  rw [triangleParameterEquiv_side]

end PoincareMT.Topology.Surface
