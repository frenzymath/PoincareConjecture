import PoincareLib.Geometry.RicciFlow.MetricComparison
import PoincareLib.Geometry.Riemannian.Curvature.NormBounds
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison

/-!
# A terminal volume bound at an earlier reference time

Actual Ricci-flow metric comparison contains a terminal ball in a larger
ball at every time in the same finite interval. The identity-map instance
of the existing normalized Hausdorff volume comparison transfers a lower
volume bound with a uniform exponential loss.

This is Morgan--Tian Lemma 3.15, p. 42, used for the reference-time input
of Proposition 5.14, pp. 90-91, and Corollary 11.3 and Claim 11.5,
pp. 269-270. See the independently reviewed terminal-earlier-volume
derivation. The given flow, metric, connection and included endpoints
are retained. Conversion to the raw Hausdorff convention of M07 is a
separate application of the existing calibration theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- A terminal ball-volume lower bound holds on a uniformly enlarged ball
at every time of the actual finite flow (Lemma 3.15, p. 42; Proposition
5.14, pp. 90-91). The volume is normalized Hausdorff volume, including
when it is infinite; completeness and curvature sign are not assumed. -/
theorem terminal_ball_volume_lower_bound_at_time
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    {T B rho v : ℝ} (G : RicciFlow n M (Icc (-T) 0))
    (hT : 0 < T) (p : M)
    (hcurv : ∀ t ∈ Icc (-T) 0, ∀ x : M,
      (G.connection t).curvatureTensorNorm x ≤ B)
    (hvolume : ENNReal.ofReal v ≤
      (G.metric 0).volumeMeasure ((G.metric 0).ball p rho)) :
    let L : ℝ := (n : ℝ) ^ 3 * max B 1
    ∀ s ∈ Icc (-T) 0,
      (G.metric 0).ball p rho ⊆
        (G.metric s).ball p (Real.exp (L * T) * rho) ∧
      ENNReal.ofReal (Real.exp (-((n : ℝ) * L * T)) * v) ≤
        (G.metric s).volumeMeasure
          ((G.metric s).ball p (Real.exp (L * T) * rho)) := by
  dsimp only
  let L : ℝ := (n : ℝ) ^ 3 * max B 1
  let E : ℝ := Real.exp (L * T)
  have hL : 0 ≤ L := mul_nonneg (by positivity)
    (zero_le_one.trans (le_max_right B 1))
  have hE : 0 < E := Real.exp_pos _
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
  have hRic (t : ℝ) (ht : t ∈ Icc (-T) 0) (x : M)
      (w : TangentSpace (𝓡 n) x) :
      |(G.connection t).ricci x w w| ≤ L * (G.metric t).inner x w w := by
    have hQ : 0 ≤ (G.metric t).inner x w w := by
      by_cases hw : w = 0
      · subst w; simp
      · exact ((G.metric t).pos x w hw).le
    have hnorm := (G.connection t).abs_ricci_quadratic_le_curvatureTensorNorm x w
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((hcurv t ht x).trans (le_max_left B 1))
        (by positivity)) hQ)
  intro s hs
  have hdisplacement : |s| ≤ T := by
    rw [abs_of_nonpos hs.2]
    linarith [hs.1]
  have hexp : Real.exp (L * |s|) ≤ E :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdisplacement hL)
  have hforward (x : M) (w : TangentSpace (𝓡 n) x) :
      (G.metric 0).tangentNorm x w ≤ E * (G.metric s).tangentNorm x w := by
    have h := G.tangentNorm_le_exp_of_ricci_bound (convex_Icc (-T) 0)
      (Subset.refl _) x w L (fun t ht => hRic t ht x w) hs hzero
    simp only [zero_sub, abs_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))
  have hbackward (x : M) (w : TangentSpace (𝓡 n) x) :
      (G.metric s).tangentNorm x w ≤ E * (G.metric 0).tangentNorm x w := by
    have h := G.tangentNorm_le_exp_of_ricci_bound (convex_Icc (-T) 0)
      (Subset.refl _) x w L (fun t ht => hRic t ht x w) hzero hs
    simp only [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))
  let U := (G.metric 0).ball p rho
  have hsubset : U ⊆ (G.metric s).ball p (E * rho) :=
    (G.metric 0).ball_subset_ball_of_tangentNorm_le (G.metric s) p rho E hE
      (fun x _ w => hbackward x w)
  refine ⟨hsubset, ?_⟩
  have hU : IsOpen U := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(G.metric 0).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨(G.metric 0).inner, (G.metric 0).toContinuousRiemannianMetric.continuous,
        fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    change IsOpen {x : M | edist p x < ENNReal.ofReal rho}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hvol := (G.metric s).volumeMeasure_image_le_of_tangentNorm_le
    (G.metric 0) (OpenPartialHomeomorph.refl M) hU (subset_univ U)
    contMDiffOn_id hE (by
      intro x _ w
      change (G.metric 0).tangentNorm x (mfderiv (𝓡 n) (𝓡 n) id x w) ≤ _
      rw [mfderiv_id]
      exact hforward x w)
    hU.measurableSet (Subset.refl U)
  change (G.metric 0).volumeMeasure (id '' U) ≤ _ at hvol
  rw [image_id] at hvol
  have htransfer := hvolume.trans
    (hvol.trans (mul_le_mul_right (MeasureTheory.measure_mono hsubset) _))
  have hpow0 : ENNReal.ofReal E ^ n ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hE)
  have hpowtop : ENNReal.ofReal E ^ n ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hdivide := (ENNReal.div_le_iff' hpow0 hpowtop).mpr htransfer
  rw [← ENNReal.ofReal_pow hE.le,
    ← ENNReal.ofReal_div_of_pos (pow_pos hE n)] at hdivide
  have hpower : E ^ n = Real.exp ((n : ℝ) * L * T) := by
    dsimp only [E]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hquotient : v / E ^ n = Real.exp (-((n : ℝ) * L * T)) * v := by
    rw [hpower, div_eq_mul_inv, ← Real.exp_neg]
    exact mul_comm _ _
  rwa [hquotient] at hdivide

end PoincareMT.M30
