import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Spheres.AnnulusPrismMap
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLClosedUnion
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundarySphere
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonProtectedDehnAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D1" => closedBall (0 : V1) 1

private theorem exists_finite_prismSide :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = prismSide := by
  obtain ⟨J, hJ, hJQ⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨I, hI, hII, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨K, hK, hKs, _⟩ := J.exists_finite_triangulation_prod I hJ hI
  exact ⟨K, hK, by simpa only [hJQ, hII, prismSide] using hKs⟩

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  (T : HamiltonProtectedDehnAnnulus L e)



theorem prismMap_piecewiseAffine
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (h : OpenPartialHomeomorph (V1 × V2) V3)
    (hsource : D1 ×ˢ (univ : Set V2) ⊆ h.source)
    (N : Set (V1 × V2))
    (hboundary : frontier (D1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h) :
    PolyhedralPLInCharts e T.prismMap (cubePrismBoundary (-1 : ℝ) 1) := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_prismSide
  have hside : PolyhedralPLInCharts e T.prismMap K.space := by
    have hlift : FinitePiecewiseAffineOn sideLift K.space :=
      (K.affineOnFaces_affine sideLift.toContinuousAffineMap).finitePiecewiseAffineOn hK
    apply (T.piecewiseAffine.comp_finitePiecewiseAffineOn K hK hlift
      (fun _ hx ↦ sideLift_mem (hKs.subset hx))).congr
    intro x hx
    exact (T.prismMap_side (hKs.subset hx)).symm
  have hcap (b : Bool) : ∃ J : SimplicialComplex ℝ E,
      J.faces.Finite ∧ J.space = prismCap b ∧ PolyhedralPLInCharts e T.prismMap J.space := by
    obtain ⟨J, hJ, hJs⟩ := exists_finite_cubePrismCap (capHeight b)
    refine ⟨J, hJ, hJs, ?_⟩
    have hlift : FinitePiecewiseAffineOn capLift J.space :=
      (J.affineOnFaces_affine capLift.toContinuousAffineMap).finitePiecewiseAffineOn hJ
    have hb (x : E) (hx : x ∈ J.space) :
        capLift x ∈ D1 ×ˢ closedBall (0 : V2) 2 := by
      have hs := hJs.subset hx
      exact capLift_mem_block ⟨hs.1, (show x.2 = capHeight b from hs.2) ▸ capHeight_mem b⟩
    have hbound (x : E) (hx : x ∈ J.space) : capLift x ∈ h.source ∩ N := by
      refine ⟨hsource ⟨(hb x hx).1, mem_univ _⟩, hboundary ?_⟩
      rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
      exact ⟨capLift_old_boundary b (hJs.subset hx), mem_univ _⟩
    have hformula (x : E) (hx : x ∈ J.space) :
        (e retained.index).symm (h (capLift x)) = T.prismMap x := by
      rw [T.prismMap_cap b (hJs.subset hx), ← retained.formula _ (hb x hx)]
      exact (e retained.index).left_inv (retained.contains _ (hb x hx))
    have hmap : MapsTo (h ∘ capLift) J.space (e retained.index).target := by
      intro x hx
      change h (capLift x) ∈ (e retained.index).target
      rw [← retained.formula _ (hb x hx)]
      exact (e retained.index).mapsTo (retained.contains _ (hb x hx))
    exact (polyhedralPLInCharts_of_one_chart_inverse J hJ
      (hPL.comp_finitePiecewiseAffineOn hlift hbound) retained.index hmap).congr hformula
  obtain ⟨K0, hK0, hK0s, hzero⟩ := hcap false
  obtain ⟨K1, hK1, hK1s, hone⟩ := hcap true
  obtain ⟨J, hJ, hJs⟩ := K0.exists_finite_triangulation_union K1 hK0 hK1
  have hcaps : PolyhedralPLInCharts e T.prismMap J.space := by
    rw [hJs]
    exact PolyhedralPLInCharts.union_of_finite he.compatible K0 K1 hK0 hK1 hzero hone
  have hall := PolyhedralPLInCharts.union_of_finite he.compatible J K hJ hK hcaps hside
  simpa only [hJs, hK0s, hK1s, hKs, ← prism_boundary_eq] using hall




theorem nonempty_chartwisePLSphere [DiscreteTopology L]
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (h : OpenPartialHomeomorph (V1 × V2) V3)
    (hsource : D1 ×ˢ (univ : Set V2) ⊆ h.source)
    (N : Set (V1 × V2))
    (hboundary : frontier (D1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h) :
    Nonempty (ChartwisePLSphere e
      (T.surface ∪ hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2))) := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_cubePrismBoundary (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨b, hb⟩ := exists_finitePL_cubePrismBoundary_sphere (by norm_num : (-1 : ℝ) < 1)
  have hmap : PolyhedralPLInCharts e T.prismMap K.space := by
    rw [hKs]
    exact T.prismMap_piecewiseAffine he h hsource N hboundary hPL retained
  have hi : InjOn T.prismMap K.space := hKs.symm ▸ T.prismMap_injOn retained
  have hex := exists_chartwisePLSphere_image K hmap hi hKs.symm.subset b.symm hb.symm
  rwa [T.prismMap_image] at hex

end PoincareConjecture.M76.HamiltonProtectedDehnAnnulus
