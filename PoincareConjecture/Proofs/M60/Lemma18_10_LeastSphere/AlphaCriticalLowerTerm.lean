import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalNormalizedEquation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalMetricNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

namespace PoincareConjecture.M60

open CoordinateExponential

local instance suLowerTermBilinearGroup {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup

local instance suLowerTermBilinearSpace {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

local instance suLowerTermTrilinearGroup {n : ℕ} :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance suLowerTermTrilinearSpace {n : ℕ} :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def suWeakAlphaLowerTerm
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)) (x : LoopPlane) :
    EuclideanSpace ℝ (Fin n) :=
  let B := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let v := fun i => V i x
  let d := suAlphaRoundFactor x + ∑ i : Fin 2, B (u x) (v i) (v i)
  suAlphaLowerTerm (christoffelBilinear B (u x)) (B (u x)) (fderiv ℝ B (u x)) v
    (suAlphaRoundFactor x)
    (fun i => fderiv ℝ suAlphaRoundFactor x (EuclideanSpace.single i 1)) d (alpha - 1)

set_option maxHeartbeats 1000000 in

theorem SUInitialGain.alpha_lowerTerm_memLp
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (S : SUWeakAlphaCoordinate g b alpha u V center R) :
    MemLp (suWeakAlphaLowerTerm g b alpha u V) 4
      (volume.restrict (Metric.ball center G.radius)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let B := g.pullbackCoefficients (chartAt E b).symm
  let Gamma := christoffelBilinear B
  let mu := volume.restrict (Metric.ball center G.radius)
  let Q := fun x => ∑ i : Fin 2, B (u x) (V i x) (V i x)
  let d := fun x => suAlphaRoundFactor x + Q x
  let dl := fun (i : Fin 2) x => fderiv ℝ suAlphaRoundFactor x (EuclideanSpace.single i 1)
  have hmap : MapsTo u (Metric.closedBall center G.radius) (extChartAt (𝓡 n) b).target :=
    fun x hx => S.coordinate_range (Metric.closedBall_subset_closedBall G.radius_lt.le hx)
  have hB := (g.contDiffOn_chartCoefficients b).continuousOn.comp G.coordinate_continuous hmap
  have hDG := ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target b) (by simp)).comp G.coordinate_continuous hmap
  have hGamma := (contDiffOn_christoffelBilinear (isOpen_extChartAt_target b)
    (g.contDiffOn_chartCoefficients b)
    (fun _ hx => g.isInvertible_chartCoefficients b hx)).continuousOn
    |>.comp G.coordinate_continuous hmap
  have hBtop : MemLp (fun x => B (u x)) ⊤ mu := suContinuous_memLp_ball hB
  have hDGtop : MemLp (fun x => fderiv ℝ B (u x)) ⊤ mu := suContinuous_memLp_ball hDG
  have hGammatop : MemLp (fun x => Gamma (u x)) ⊤ mu := suContinuous_memLp_ball hGamma
  have hcol (p : ℕ) (hp : 1 ≤ p) (i : Fin 2) : MemLp (V i) (p : ℝ≥0∞) mu := by
    simpa using G.column_memLp (p : ℝ) (by exact_mod_cast hp) i
  let : ENNReal.HolderTriple 32 32 16 := ENNReal.HolderTriple.of_toReal
    ⟨by norm_num, by norm_num, by norm_num⟩
  let : ENNReal.HolderTriple 16 16 8 := ENNReal.HolderTriple.of_toReal
    ⟨by norm_num, by norm_num, by norm_num⟩
  let : ENNReal.HolderTriple 8 8 4 := ENNReal.HolderTriple.of_toReal
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hquad (i : Fin 2) : MemLp (fun x => B (u x) (V i x) (V i x)) 8 mu := by
    have hb : MemLp (fun x => B (u x) (V i x)) 16 mu :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
        (p := 16) (q := ⊤) 16 (hcol 16 (by norm_num) i) hBtop
    simpa only using! (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
      (p := 16) (q := 16) 8 (hcol 16 (by norm_num) i) hb
  have hQ : MemLp Q 8 mu := memLp_finsetSum _ (fun i _ => hquad i)
  have hInvCont : Continuous (fun x => (suAlphaRoundFactor x)⁻¹) :=
    suRoundFactor_smooth_pos.1.continuous.inv₀ (fun x => (suRoundFactor_smooth_pos.2 x).ne')
  have hInv : MemLp (fun x => (suAlphaRoundFactor x)⁻¹) ⊤ mu :=
    suContinuous_memLp_ball hInvCont.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_closedBall center G.radius).bddAbove_image hInvCont.norm.continuousOn
  obtain ⟨kappa, _, hk, _, hb⟩ := S.coefficient_bounds
  have hdInv : MemLp (fun x => (d x)⁻¹) ⊤ mu := by
    apply memLp_top_of_bound
      ((suRoundFactor_smooth_pos.1.continuous.aemeasurable.add
        hQ.aestronglyMeasurable.aemeasurable).inv.aestronglyMeasurable) C
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hxr := Metric.closedBall_subset_closedBall G.radius_lt.le
      (Metric.ball_subset_closedBall hx)
    have hQ0 : 0 ≤ Q x := Finset.sum_nonneg fun i _ =>
      (mul_nonneg hk.le (sq_nonneg _)).trans ((hb x hxr).2.2 (V i x))
    have hl := suRoundFactor_smooth_pos.2 x
    calc
      _ = (d x)⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr (by dsimp [d]; positivity))
      _ ≤ (suAlphaRoundFactor x)⁻¹ := inv_anti₀ hl (le_add_of_nonneg_right hQ0)
      _ ≤ C := (le_abs_self _).trans (hC (mem_image_of_mem _ (Metric.ball_subset_closedBall hx)))
  have hdl (i : Fin 2) : MemLp (dl i) ⊤ mu := suContinuous_memLp_ball
    (((suRoundFactor_smooth_pos.1.continuous_fderiv (by simp)).clm_apply
      continuous_const).continuousOn)
  have hconn (i : Fin 2) : MemLp (fun x => Gamma (u x) (V i x) (V i x)) 4 mu :=
    (ContinuousLinearMap.apply ℝ E (E := E)).memLp_of_bilin (p := 8) (q := 8) 4
      (hcol 8 (by norm_num) i)
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) (E := E)).memLp_of_bilin
        (p := 8) (q := ⊤) 8 (hcol 8 (by norm_num) i) hGammatop)
  have hcubic (i j : Fin 2) :
      MemLp (fun x => fderiv ℝ B (u x) (V i x) (V j x) (V j x)) 8 mu := by
    have h1 : MemLp (fun x => fderiv ℝ B (u x) (V i x)) 32 mu := by
      simpa only using! (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
        (p := 32) (q := ⊤) 32 (hcol 32 (by norm_num) i) hDGtop
    have h2 : MemLp (fun x => fderiv ℝ B (u x) (V i x) (V j x)) 16 mu :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
        (p := 32) (q := 32) 16 (hcol 32 (by norm_num) j) h1
    exact (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
      (p := 16) (q := 16) 8 (hcol 16 (by norm_num) j) h2
  have hlower (i : Fin 2) : MemLp (fun x =>
      ((∑ j : Fin 2, fderiv ℝ B (u x) (V i x) (V j x) (V j x)) -
        Q x * dl i x / suAlphaRoundFactor x) • V i x) 4 mu := by
    have hs : MemLp (fun x => ∑ j : Fin 2, fderiv ℝ B (u x) (V i x) (V j x) (V j x)) 8 mu :=
      memLp_finsetSum _ (fun j _ => hcubic i j)
    have hq : MemLp (fun x => Q x * dl i x / suAlphaRoundFactor x) 8 mu := by
      simpa only [div_eq_mul_inv] using hInv.mul' (r := 8) ((hdl i).mul' (r := 8) hQ)
    exact (hcol 8 (by norm_num) i).smul (hs.sub hq)
  have h1 := memLp_finsetSum Finset.univ (fun i _ => hconn i)
  have h2 := memLp_finsetSum Finset.univ (fun i _ => hlower i)
  have h := h1.neg.sub (h2.smul (hdInv.const_mul (alpha - 1)))
  simpa only [suWeakAlphaLowerTerm, suAlphaLowerTerm, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, div_eq_mul_inv, B, Gamma, Q, d, dl] using! h

end PoincareConjecture.M60

end
