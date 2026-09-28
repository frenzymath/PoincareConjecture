import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedCoordinateVariation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64BoundaryCoefficients_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryCoefficients_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64BoundaryCoefficients_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryCoefficients_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace




theorem m64ChartCoordinate_coefficient_bounds
    (g : RiemannianMetric n M) (b : M) {u : LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hu : ContinuousOn u (closedBall a R))
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    ∃ kappa C : ℝ, 0 < kappa ∧ 0 < C ∧
      ∀ p ∈ closedBall a R, ‖G (u p)‖ ≤ C ∧ ‖fderiv ℝ G (u p)‖ ≤ C ∧
        ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G (u p) v v := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let K := u '' closedBall a R
  have hK : IsCompact K := (isCompact_closedBall a R).image_of_continuousOn hu
  have hKt : K ⊆ (extChartAt (𝓡 n) b).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact huT hp
  obtain ⟨kappa, C, hk, hC, -, hb, hpos⟩ := M60.suAlpha_coordinate_metric_bounds g b hK hKt
  have hd : ContinuousOn (fderiv ℝ G) K :=
    ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target b) (by simp)).mono hKt
  obtain ⟨D, hD⟩ := hK.bddAbove_image (continuous_norm.comp_continuousOn hd)
  refine ⟨kappa, C + max D 0 + 1, hk, by positivity, fun p hp => ?_⟩
  have hpK : u p ∈ K := mem_image_of_mem _ hp
  refine ⟨(hb _ hpK).trans (by have := le_max_right D 0; linarith), ?_, hpos _ hpK⟩
  exact (hD (mem_image_of_mem _ hpK)).trans (by have := le_max_left D 0; linarith)

set_option maxHeartbeats 800000 in





theorem m64WeightedChart_flux_source_memLp
    (g : RiemannianMetric n M) (b : M) (modulus : ℝ)
    {u : LoopPlane → E} {V : Fin 2 → LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hu : ContinuousOn u (closedBall a R))
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R))) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    (∀ j : Fin n, ∀ i : Fin 2, MemLp
      (fun p => (if i = 0 then modulus else modulus⁻¹) *
        G (u p) (V i p) (EuclideanSpace.single j 1)) 2 (volume.restrict (ball a R))) ∧
    ∀ j : Fin n, IntegrableOn (fun p =>
      -(modulus * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V 0 p) (V 0 p) +
        modulus⁻¹ * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V 1 p) (V 1 p)) / 2)
      (ball a R) := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let mu := volume.restrict (ball a R)
  obtain ⟨kappa, C, -, -, hbound⟩ := m64ChartCoordinate_coefficient_bounds g b hu huT
  have hB := (g.contDiffOn_chartCoefficients b).continuousOn.comp hu huT
  have hD := ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target b) (by simp)).comp hu huT
  have hGM : MemLp (fun p => G (u p)) ⊤ mu := memLp_top_of_bound
    ((hB.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
      exact (hbound p (ball_subset_closedBall hp)).1)
  have hDM : MemLp (fun p => fderiv ℝ G (u p)) ⊤ mu := memLp_top_of_bound
    ((hD.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
      exact (hbound p (ball_subset_closedBall hp)).2.1)
  have hGV (i : Fin 2) : MemLp (fun p => G (u p) (V i p)) 2 mu :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) («E» := E)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (hV i) hGM
  refine ⟨?_, ?_⟩
  · intro j i
    exact (((ContinuousLinearMap.apply ℝ ℝ («E» := E)) (EuclideanSpace.single j 1)
      ).comp_memLp' (hGV i)).const_mul _
  · intro j
    have hDG : MemLp (fun p => fderiv ℝ G (u p) (EuclideanSpace.single j 1)) ⊤ mu :=
      (((ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) («E» := E))
        (EuclideanSpace.single j 1)).comp_memLp' hDM)
    have hquad (i : Fin 2) : Integrable (fun p =>
        fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) mu := by
      have hfirst := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) («E» := E)).memLp_of_bilin
        (p := 2) (q := ⊤) 2 (hV i) hDG
      exact memLp_one_iff_integrable.mp
        ((ContinuousLinearMap.apply ℝ ℝ («E» := E)).memLp_of_bilin
          (p := 2) (q := 2) 1 (hV i) hfirst)
    exact (((hquad 0).const_mul modulus).add ((hquad 1).const_mul modulus⁻¹)).neg.div_const 2

end PoincareConjecture
