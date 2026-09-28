import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Spheres.PrismMap
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLClosedUnion
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundarySphere
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonProtectedDehnDisks

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1

private theorem exists_finite_prismSide :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = prismSide := by
  obtain ⟨J, hJ, hJQ⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨I, hI, hII, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : -(3 / 2 : ℝ) < 3 / 2)
  obtain ⟨K, hK, hKs, _⟩ := J.exists_finite_triangulation_prod I hJ hI
  exact ⟨K, hK, by simpa only [hJQ, hII, prismSide] using hKs⟩

variable {L : Submodule ℤ V1} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3}
  (T : HamiltonProtectedDehnDisks L e)



theorem prismMap_piecewiseAffine
    (he : PLDomain e (latticeHandleDomain (Fin 2) (Fin 1) L))
    (h : OpenPartialHomeomorph (V2 × V1) V3)
    (hsource : D ×ˢ (univ : Set V1) ⊆ h.source)
    (N : Set (V2 × V1))
    (hboundary : frontier (D ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) :
    PolyhedralPLInCharts e T.prismMap (cubePrismBoundary (-(3 / 2 : ℝ)) (3 / 2)) := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_prismSide
  have hside : PolyhedralPLInCharts e T.prismMap K.space := by
    have hlift : FinitePiecewiseAffineOn prismLift K.space :=
      (K.affineOnFaces_affine prismLift.toContinuousAffineMap).finitePiecewiseAffineOn hK
    have hbound (x : E) (hx : x ∈ K.space) :
        prismLift x ∈ h.source ∩ N := by
      have hs := hKs.subset hx
      refine ⟨hsource ⟨sphere_subset_closedBall hs.1, mem_univ _⟩, hboundary ?_⟩
      rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
      exact ⟨hs.1, mem_univ _⟩
    have hformula (x : E) (hx : x ∈ K.space) :
        (e retained.index).symm (h (prismLift x)) = T.prismMap x := by
      have hs := hKs.subset hx
      have hb := prismLift_mem_block ⟨sphere_subset_closedBall hs.1, hs.2⟩
      rw [T.prismMap_side hs, ← retained.formula _ hb]
      exact (e retained.index).left_inv (retained.contains _ hb)
    have hmap : MapsTo (h ∘ prismLift) K.space (e retained.index).target := by
      intro x hx
      have hs := hKs.subset hx
      have hb := prismLift_mem_block ⟨sphere_subset_closedBall hs.1, hs.2⟩
      change h (prismLift x) ∈ (e retained.index).target
      rw [← retained.formula _ hb]
      exact (e retained.index).mapsTo (retained.contains _ hb)
    exact (polyhedralPLInCharts_of_one_chart_inverse K hK
      (hPL.comp_finitePiecewiseAffineOn hlift hbound) retained.index hmap).congr hformula
  have hcap (b : Bool) : ∃ J : SimplicialComplex ℝ E,
      J.faces.Finite ∧ J.space = prismCap b ∧ PolyhedralPLInCharts e T.prismMap J.space := by
    obtain ⟨J, hJ, hJs⟩ := exists_finite_cubePrismCap (capHeight b)
    refine ⟨J, hJ, hJs, ?_⟩
    have hfst : FinitePiecewiseAffineOn (Prod.fst : E → V2) J.space :=
      (J.affineOnFaces_affine
        (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hJ
    apply ((T.piecewiseAffine b).comp_finitePiecewiseAffineOn J hJ hfst
      (fun _ hx ↦ (hJs.subset hx).1)).congr
    intro x hx
    exact (T.prismMap_cap b (hJs.subset hx)).symm
  obtain ⟨K0, hK0, hK0s, hzero⟩ := hcap false
  obtain ⟨K1, hK1, hK1s, hone⟩ := hcap true
  obtain ⟨J, hJ, hJs⟩ := K0.exists_finite_triangulation_union K1 hK0 hK1
  have hcaps : PolyhedralPLInCharts e T.prismMap J.space := by
    rw [hJs]
    exact PolyhedralPLInCharts.union_of_finite he.compatible K0 K1 hK0 hK1 hzero hone
  have hall := PolyhedralPLInCharts.union_of_finite he.compatible J K hJ hK hcaps hside
  simpa only [hJs, hK0s, hK1s, hKs, ← prism_boundary_eq] using hall




theorem nonempty_chartwisePLSphere [DiscreteTopology L]
    (he : PLDomain e (latticeHandleDomain (Fin 2) (Fin 1) L))
    (h : OpenPartialHomeomorph (V2 × V1) V3)
    (hsource : D ×ˢ (univ : Set V1) ⊆ h.source)
    (N : Set (V2 × V1))
    (hboundary : frontier (D ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) :
    Nonempty (ChartwisePLSphere e
      ((⋃ b, T.surface b) ∪ hamiltonAttachingBlock (Fin 2) (Fin 1) L (3 / 2))) := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_cubePrismBoundary
    (by norm_num : -(3 / 2 : ℝ) < 3 / 2)
  obtain ⟨b, hb⟩ := exists_finitePL_cubePrismBoundary_sphere
    (by norm_num : -(3 / 2 : ℝ) < 3 / 2)
  have hmap : PolyhedralPLInCharts e T.prismMap K.space := by
    rw [hKs]
    exact T.prismMap_piecewiseAffine he h hsource N hboundary hPL retained
  have hi : InjOn T.prismMap K.space := hKs.symm ▸ T.prismMap_injOn retained
  have hex := exists_chartwisePLSphere_image K hmap hi hKs.symm.subset b.symm hb.symm
  rwa [T.prismMap_image] at hex

end PoincareConjecture.M76.HamiltonProtectedDehnDisks
