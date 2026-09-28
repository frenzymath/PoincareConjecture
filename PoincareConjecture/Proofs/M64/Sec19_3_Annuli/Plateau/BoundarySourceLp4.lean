import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64BoundarySourceLp4_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundarySourceLp4_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 800000 in

theorem m64WeightedChart_source_memLp_four
    (g : RiemannianMetric n M) (b : M) (modulus : ℝ)
    {u : LoopPlane → E} {V : Fin 2 → LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hu : ContinuousOn u (closedBall a R))
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hV : ∀ i, MemLp (V i) 8 (volume.restrict (ball a R))) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    ∀ j : Fin n, MemLp (fun p =>
      -(modulus * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V 0 p) (V 0 p) +
        modulus⁻¹ * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V 1 p) (V 1 p)) / 2)
      4 (volume.restrict (ball a R)) := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let mu := volume.restrict (ball a R)
  obtain ⟨kappa, C, -, -, hbound⟩ := m64ChartCoordinate_coefficient_bounds g b hu huT
  have hD := ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target b) (by simp)).comp hu huT
  have hDM : MemLp (fun p => fderiv ℝ G (u p)) ⊤ mu := memLp_top_of_bound
    ((hD.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
      exact (hbound p (ball_subset_closedBall hp)).2.1)
  let : ENNReal.HolderTriple 8 8 4 := ENNReal.HolderTriple.of_toReal
    ⟨by norm_num, by norm_num, by norm_num⟩
  dsimp only
  intro j
  have hDG : MemLp (fun p => fderiv ℝ G (u p) (EuclideanSpace.single j 1)) ⊤ mu :=
    (((ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) («E» := E))
      (EuclideanSpace.single j 1)).comp_memLp' hDM)
  have hquad (i : Fin 2) : MemLp (fun p =>
      fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) 4 mu := by
    have hfirst : MemLp (fun p =>
        fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V i p)) 8 mu :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) («E» := E)).memLp_of_bilin
        (p := 8) (q := ⊤) 8 (hV i) hDG
    exact (ContinuousLinearMap.apply ℝ ℝ («E» := E)).memLp_of_bilin
      (p := 8) (q := 8) 4 (hV i) hfirst
  have hsum :=
    ((((hquad 0).const_mul modulus).add ((hquad 1).const_mul modulus⁻¹)).neg.const_mul
      (2⁻¹ : ℝ))
  apply hsum.ae_eq
  filter_upwards [] with p
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

end PoincareConjecture
