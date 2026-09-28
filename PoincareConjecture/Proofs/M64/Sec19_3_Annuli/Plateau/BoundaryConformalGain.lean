import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateCoefficients
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNaturalGrowthBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64ConformalGain_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64ConformalGain_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64ConformalGain_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64ConformalGain_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem m64WeightedConformal_normal_column_bound
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v0 v1 : E) {kappa C modulus : ℝ}
    (hk : 0 < kappa) (hG : ‖G‖ ≤ C)
    (hpos : kappa * ‖v1‖ ^ 2 ≤ G v1 v1)
    (hconf : G v1 v1 = modulus ^ 2 * G v0 v0) :
    ‖v1‖ ≤ (|modulus| * (C / kappa + 1)) * ‖v0‖ := by
  have hC : 0 ≤ C := (norm_nonneg G).trans hG
  have hc : 0 ≤ C / kappa := div_nonneg hC hk.le
  have hratio : C ≤ kappa * (C / kappa + 1) ^ 2 := by
    have hidentity : kappa * (C / kappa) = C := by field_simp
    have hsq : C / kappa ≤ (C / kappa + 1) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq hk.le
    simpa only [hidentity] using h
  have h00 : G v0 v0 ≤ C * ‖v0‖ ^ 2 := by
    exact (le_abs_self _).trans ((m64Bilinear_norm_bound G hG v0 v0).trans_eq (by ring))
  have hsquare : kappa * ‖v1‖ ^ 2 ≤
      kappa * ((|modulus| * (C / kappa + 1)) * ‖v0‖) ^ 2 := by
    calc
      _ ≤ G v1 v1 := hpos
      _ = modulus ^ 2 * G v0 v0 := hconf
      _ ≤ modulus ^ 2 * (C * ‖v0‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h00 (sq_nonneg _)
      _ ≤ modulus ^ 2 * (kappa * (C / kappa + 1) ^ 2 * ‖v0‖ ^ 2) := by gcongr
      _ = _ := by rw [mul_pow, mul_pow, sq_abs]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    ((mul_le_mul_iff_of_pos_left hk).mp hsquare)

theorem m64WeightedConformal_normal_memLp
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {p : ℝ≥0∞}
    (G : X → E →L[ℝ] E →L[ℝ] ℝ) {v0 v1 : X → E} {kappa C modulus : ℝ}
    (hk : 0 < kappa) (hv0 : MemLp v0 p mu) (hv1 : AEStronglyMeasurable v1 mu)
    (hdata : ∀ᵐ x ∂mu, ‖G x‖ ≤ C ∧ kappa * ‖v1 x‖ ^ 2 ≤ G x (v1 x) (v1 x) ∧
      G x (v1 x) (v1 x) = modulus ^ 2 * G x (v0 x) (v0 x)) :
    MemLp v1 p mu := by
  apply (hv0.norm.const_mul (|modulus| * (C / kappa + 1))).mono' hv1
  filter_upwards [hdata] with x hx
  exact m64WeightedConformal_normal_column_bound (G x) (v0 x) (v1 x) hk hx.1 hx.2.1 hx.2.2

set_option maxHeartbeats 800000 in

theorem m64WeightedChart_source_memLp_two
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (modulus : ℝ)
    {u : LoopPlane → E} {V : Fin 2 → LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hu : ContinuousOn u (closedBall a R))
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hV : ∀ i, MemLp (V i) 4 (volume.restrict (ball a R))) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    ∀ j : Fin n, MemLp (fun p =>
      -(modulus * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V 0 p) (V 0 p) +
        modulus⁻¹ * fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V 1 p) (V 1 p)) / 2)
      2 (volume.restrict (ball a R)) := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let mu := volume.restrict (ball a R)
  obtain ⟨kappa, C, -, -, hbound⟩ := m64ChartCoordinate_coefficient_bounds g b hu huT
  have hD := ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target b) (by simp)).comp hu huT
  have hDM : MemLp (fun p => fderiv ℝ G (u p)) ⊤ mu := memLp_top_of_bound
    ((hD.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
      exact (hbound p (ball_subset_closedBall hp)).2.1)
  dsimp only
  intro j
  let : ENNReal.HolderTriple 4 4 2 := ENNReal.HolderTriple.of_toReal
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hDG : MemLp (fun p => fderiv ℝ G (u p) (EuclideanSpace.single j 1)) ⊤ mu :=
    (((ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) («E» := E))
      (EuclideanSpace.single j 1)).comp_memLp' hDM)
  have hquad (i : Fin 2) : MemLp (fun p =>
      fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) 2 mu := by
    have hfirst : MemLp (fun p =>
        fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V i p)) 4 mu :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) («E» := E)).memLp_of_bilin
        (p := 4) (q := ⊤) 4 (hV i) hDG
    exact (ContinuousLinearMap.apply ℝ ℝ («E» := E)).memLp_of_bilin
      (p := 4) (q := 4) 2 (hV i) hfirst
  have hsum :=
    ((((hquad 0).const_mul modulus).add ((hquad 1).const_mul modulus⁻¹)).neg.const_mul
      (2⁻¹ : ℝ))
  apply hsum.ae_eq
  filter_upwards [] with p
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

end PoincareConjecture
