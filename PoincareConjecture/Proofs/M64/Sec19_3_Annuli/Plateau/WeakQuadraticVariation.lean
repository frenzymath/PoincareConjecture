import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaFirstVariation












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

private theorem quadratic_ae_clm_apply {X V W : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {mu : Measure X} {A : X → V →L[ℝ] W} {v : X → V}
    (hA : AEStronglyMeasurable A mu) (hv : AEStronglyMeasurable v mu) :
    AEStronglyMeasurable (fun x => A x (v x)) mu :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hv)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64WeakQuadraticVariation_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance m64WeakQuadraticVariation_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance m64WeakQuadraticVariation_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance m64WeakQuadraticVariation_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1600000 in




theorem m64WeakQuadratic_integral_firstVariation
    (g : RiemannianMetric n M) (b : M)
    (u phi V D : LoopPlane → E) (hu : Continuous u) (hphi : Continuous phi) (hD : Continuous D)
    (a : LoopPlane) (R : ℝ) (hV : MemLp V 2 (volume.restrict (ball a R)))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 n) b).target)
    {delta : ℝ} (hdelta : 0 < delta)
    (hrange : ∀ t : ℝ, |t| < delta → ∀ p ∈ closedBall a R, u p + t • phi p ∈ K) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let J := fun (t : ℝ) (p : LoopPlane) =>
      G (u p + t • phi p) (V p + t • D p) (V p + t • D p)
    let rate := fun p => fderiv ℝ G (u p) (phi p) (V p) (V p) +
      G (u p) (D p) (V p) + G (u p) (V p) (D p)
    IntegrableOn rate (ball a R) ∧
      HasDerivAt (fun t : ℝ => ∫ p in ball a R, J t p) (∫ p in ball a R, rate p) 0 := by
  let mu := volume.restrict (ball a R)
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let U := fun (t : ℝ) (p : LoopPlane) => u p + t • phi p
  let W := fun (t : ℝ) (p : LoopPlane) => V p + t • D p
  let J := fun (t : ℝ) (p : LoopPlane) => G (U t p) (W t p) (W t p)
  let dJ := fun (t : ℝ) (p : LoopPlane) =>
    fderiv ℝ G (U t p) (phi p) (W t p) (W t p) +
      G (U t p) (D p) (W t p) + G (U t p) (W t p) (D p)
  let A := fun p : LoopPlane => 1 + ‖V p‖
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hGB : ContinuousOn G K := (g.contDiffOn_chartCoefficients b).continuousOn.mono hKt
  have hGD : ContinuousOn (fderiv ℝ G) K :=
    ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target b) (by simp)).mono hKt
  obtain ⟨C0, hC0⟩ := hK.bddAbove_image
    ((continuous_norm.comp_continuousOn hGB).add (continuous_norm.comp_continuousOn hGD))
  let C := max C0 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcoeff (y : E) (hy : y ∈ K) : ‖G y‖ ≤ C ∧ ‖fderiv ℝ G y‖ ≤ C := by
    have hh := (hC0 (mem_image_of_mem _ hy)).trans (le_max_left C0 1)
    exact ⟨le_trans (le_add_of_nonneg_right (norm_nonneg _)) hh,
      le_trans (le_add_of_nonneg_left (norm_nonneg _)) hh⟩
  obtain ⟨P0, hP0⟩ := (isCompact_closedBall a R).bddAbove_image
    (hphi.norm.add hD.norm).continuousOn
  let P := max P0 1
  have hP : 0 < P := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have htest (p : LoopPlane) (hp : p ∈ closedBall a R) : ‖phi p‖ ≤ P ∧ ‖D p‖ ≤ P := by
    have hh := (hP0 (mem_image_of_mem _ hp)).trans (le_max_left P0 1)
    exact ⟨le_trans (le_add_of_nonneg_right (norm_nonneg _)) hh,
      le_trans (le_add_of_nonneg_left (norm_nonneg _)) hh⟩
  have hA : MemLp A 2 mu := (memLp_const (1 : ℝ)).add hV.norm
  have hA2 : Integrable (fun p => A p ^ 2) mu := by
    simpa only [pow_two] using memLp_one_iff_integrable.mp (hA.mul' hA)
  let bound := fun p => (3 * C * P * (1 + P) ^ 2) * A p ^ 2
  have hboundI : Integrable bound mu := hA2.const_mul _
  have hzero : |(0 : ℝ)| < delta := by simpa using hdelta
  have hU (t : ℝ) : Continuous (U t) := hu.add (hphi.const_smul t)
  have hW (t : ℝ) : AEStronglyMeasurable (W t) mu :=
    hV.aestronglyMeasurable.add (hD.const_smul t).aestronglyMeasurable
  have hGm (t : ℝ) (ht : |t| < delta) :
      AEStronglyMeasurable (fun p => G (U t p)) mu ∧
        AEStronglyMeasurable (fun p => fderiv ℝ G (U t p)) mu := by
    have hmap : MapsTo (U t) (ball a R) K := fun p hp => hrange t ht p (ball_subset_closedBall hp)
    exact ⟨(hGB.comp (hU t).continuousOn hmap).aestronglyMeasurable measurableSet_ball,
      (hGD.comp (hU t).continuousOn hmap).aestronglyMeasurable measurableSet_ball⟩
  have hJm (t : ℝ) (ht : |t| < delta) : AEStronglyMeasurable (J t) mu :=
    quadratic_ae_clm_apply (quadratic_ae_clm_apply (hGm t ht).1 (hW t)) (hW t)
  have hdJm : AEStronglyMeasurable (dJ 0) mu :=
    ((quadratic_ae_clm_apply (quadratic_ae_clm_apply
      (quadratic_ae_clm_apply (hGm 0 hzero).2 hphi.aestronglyMeasurable) (hW 0)) (hW 0)).add
        (quadratic_ae_clm_apply (quadratic_ae_clm_apply
          (hGm 0 hzero).1 hD.aestronglyMeasurable) (hW 0))).add
      (quadratic_ae_clm_apply (quadratic_ae_clm_apply
        (hGm 0 hzero).1 (hW 0)) hD.aestronglyMeasurable)
  have hJ0 : Integrable (J 0) mu := by
    apply (hA2.const_mul C).mono' (hJm 0 hzero)
    filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
    have hc := (hcoeff (U 0 p) (hrange 0 hzero p (ball_subset_closedBall hp))).1
    simp only [U, zero_smul, add_zero] at hc
    change ‖G (U 0 p) (W 0 p) (W 0 p)‖ ≤ C * A p ^ 2
    simp only [U, W, zero_smul, add_zero]
    calc
      _ ≤ ‖G (u p)‖ * ‖V p‖ * ‖V p‖ := (G (u p)).le_opNorm₂ _ _
      _ ≤ C * A p * A p := by gcongr <;> first | exact hc | exact le_add_of_nonneg_left zero_le_one
      _ = _ := by ring
  have hdiff : ∀ᵐ p ∂mu, ∀ t ∈ ball (0 : ℝ) (min delta 1),
      HasDerivAt (fun s => J s p) (dJ t p) t := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with p hp t ht
    have ht' : |t| < delta := lt_of_lt_of_le
      (by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht) (min_le_left _ _)
    have htarget := hKt (hrange t ht' p (ball_subset_closedBall hp))
    have hu' : HasDerivAt (fun s : ℝ => U s p) (phi p) t := by
      simpa [U] using ((hasDerivAt_id t).smul_const (phi p)).const_add (u p)
    have hw' : HasDerivAt (fun s : ℝ => W s p) (D p) t := by
      simpa [W] using ((hasDerivAt_id t).smul_const (D p)).const_add (V p)
    have hg := ((g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds htarget)).differentiableAt (by simp)
    have hh := ((hg.hasFDerivAt.comp_hasDerivAt (l := G)
      (f := fun s : ℝ => U s p) t hu').clm_apply hw').clm_apply hw'
    simpa only [J, dJ, Function.comp_apply, add_apply] using hh
  have hbound : ∀ᵐ p ∂mu, ∀ t ∈ ball (0 : ℝ) (min delta 1), ‖dJ t p‖ ≤ bound p := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with p hp t ht
    have ht0 : |t| < min delta 1 := by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
    have ht' := lt_of_lt_of_le ht0 (min_le_left _ _)
    have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht0 (min_le_right _ _)).le
    have hc := hcoeff (U t p) (hrange t ht' p (ball_subset_closedBall hp))
    have htp := htest p (ball_subset_closedBall hp)
    have hA1 : 1 ≤ A p := le_add_of_nonneg_right (norm_nonneg _)
    have hv : ‖W t p‖ ≤ (1 + P) * A p := by
      have h0 := norm_add_le (V p) (t • D p)
      rw [norm_smul, Real.norm_eq_abs] at h0
      have h1 := mul_le_mul ht1 htp.2 (norm_nonneg _) zero_le_one
      dsimp only [W, A]
      nlinarith [norm_nonneg (V p), hP]
    have hm : ‖fderiv ℝ G (U t p) (phi p) (W t p) (W t p)‖ ≤
        C * P * ((1 + P) * A p) ^ 2 := by
      calc
        _ ≤ ‖fderiv ℝ G (U t p) (phi p)‖ * ‖W t p‖ * ‖W t p‖ :=
          (fderiv ℝ G (U t p) (phi p)).le_opNorm₂ _ _
        _ ≤ (‖fderiv ℝ G (U t p)‖ * ‖phi p‖) * ‖W t p‖ * ‖W t p‖ := by
          gcongr
          exact (fderiv ℝ G (U t p)).le_opNorm _
        _ ≤ C * P * ((1 + P) * A p) * ((1 + P) * A p) := by
          gcongr <;> first | exact hc.2 | exact htp.1
        _ = _ := by ring
    have hl : ‖G (U t p) (D p) (W t p)‖ ≤ C * P * ((1 + P) * A p) := by
      exact ((G (U t p)).le_opNorm₂ _ _).trans (by gcongr <;> first | exact hc.1 | exact htp.2)
    have hr : ‖G (U t p) (W t p) (D p)‖ ≤ C * P * ((1 + P) * A p) := by
      have h := ((G (U t p)).le_opNorm₂ (W t p) (D p)).trans
        (show ‖G (U t p)‖ * ‖W t p‖ * ‖D p‖ ≤ C * ((1 + P) * A p) * P from by
          gcongr <;> first | exact hc.1 | exact hv | exact htp.2)
      exact h.trans_eq (by ring)
    have ha : 1 ≤ (1 + P) * A p := by nlinarith
    have hsq : (1 + P) * A p ≤ ((1 + P) * A p) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ C * P by positivity)
    have hsum := (norm_add_le
      (fderiv ℝ G (U t p) (phi p) (W t p) (W t p) + G (U t p) (D p) (W t p))
      (G (U t p) (W t p) (D p))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    dsimp only [dJ, bound]
    nlinarith
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds (0 : ℝ) (lt_min hdelta zero_lt_one))
    (Filter.mem_of_superset (ball_mem_nhds (0 : ℝ) hdelta)
      (fun t ht => hJm t (by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht)))
    hJ0 hdJm hbound hboundI hdiff
  simpa only [J, dJ, U, W, zero_smul, add_zero, IntegrableOn, mu] using hh

end PoincareConjecture
