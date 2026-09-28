import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.SphereEulerCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.CircleCapEulerCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem finitePL_disk_rim_surfaceEulerCount
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D r : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D r)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (hLr : L.space = r) :
    L.surfaceEulerCount = 0 := by
  let c : (ℝ × ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨H,hH,hHr⟩ := hD.exists_cube_chart c
  let e := H.restrictSubsets hD.1 isClosed_closedBall.frontier_subset hHr
  have he : e.IsFinitePL := hH.restrictSubsets hD.1
    isClosed_closedBall.frontier_subset hHr L hL hLr
  have hr : frontier (closedBall (0 : Fin 2 → ℝ) 1) = sphere (0 : Fin 2 → ℝ) 1 :=
    frontier_closedBall _ (by norm_num)
  let G := (Homeomorph.setCongr hr.symm).trans
    (e.symm.trans (Homeomorph.setCongr hLr.symm))
  have hG : G.IsFinitePL := he.symm.setCongr hr hLr.symm
  exact Dehn.Annuli.circle_surfaceEulerCount L hL G hG

end PoincareConjecture.M76.PrismBelt
