import PoincareConjecture.Proofs.M47.SeedNormalizedAccess
import PoincareConjecture.Proofs.M47.SeedNormalizedFlow
import PoincareConjecture.Proofs.M47.SeedM15Ordinary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem seedM15_normalized_history_volume
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3)
    {l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 1 l0 V)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    {b T tau r : ℝ} (hbt : b < T) (F : RicciFlow 3 M (Icc b T)) (x : M)
    (htau : 0 < tau) (htauAge : tau < T - b)
    (E : Set M) (hE : IsOpen E)
    (haccess : ∀ y ∈ E, reducedLength F T x y tau ≤ l0)
    (hvolume : ENNReal.ofReal (V * Real.sqrt (T - b) ^ 3) ≤
      calibratedMetricVolume (F.metric (T - tau)) E)
    (hr : 0 < r) (hrtau : r ^ 2 ≤ tau)
    (hcurv : ∀ s ∈ Icc (T - r ^ 2) T, ∀ y ∈ (F.metric T).ball x r,
      (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (U.kappa * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  have hd : 0 < T - b := sub_pos.mpr hbt
  have hsqrt : 0 < Real.sqrt (T - b) := Real.sqrt_pos.mpr hd
  have hsqrt2 : Real.sqrt (T - b) ^ 2 = T - b := Real.sq_sqrt hd.le
  let sigma := tau / (T - b)
  let rho := r / Real.sqrt (T - b)
  have hsigma : 0 < sigma := div_pos htau hd
  have hsigmaOne : sigma < 1 := (div_lt_one hd).mpr htauAge
  have hrho : 0 < rho := div_pos hr hsqrt
  have hclock : (T - b) * sigma = tau := by dsimp only [sigma]; field_simp
  have hrho2 : (T - b) * rho ^ 2 = r ^ 2 := by
    dsimp only [rho]
    rw [div_pow, hsqrt2, mul_div_cancel₀ _ hd.ne']
  have hrhoAge : rho ^ 2 ≤ sigma := by nlinarith [hrtau]
  obtain ⟨G, hG⟩ := exists_seed_normalized_flow hM13 hbt F
  have hback (s : ℝ) : b + (T - b) * (1 - s) = T - (T - b) * s := by ring
  have hmetric (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) sigma)
      (y : M) (v w : TangentSpace (𝓡 3) y) :
      (G.metric (1 - s)).inner y v w =
        (T - b)⁻¹ * (F.metric (T - (T - b) * s)).inner y v w := by
    simpa only [hback] using (hG (1 - s)).1 y v w
  have hscalar (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) sigma) (y : M) :
      (G.connection (1 - s)).scalarCurvature y =
        (T - b) * (F.connection (T - (T - b) * s)).scalarCurvature y := by
    exact ((hG (1 - s)).2.1 y).trans
      (congrArg (fun t : ℝ => (T - b) * (F.connection t).scalarCurvature y) (hback s))
  have hnormalizedAccess (y : M) (hy : y ∈ E) : reducedLength G 1 x y sigma ≤ l0 := by
    have h := seed_compact_normalized_access hOrdinary hbt hsigma hsigmaOne.le
      F G hmetric hscalar x y
    rw [hclock] at h
    exact h.trans (haccess y hy)
  have hseedClock : b + (T - b) * (1 - sigma) = T - tau := by rw [hback, hclock]
  have hfactorPos : 0 < (Real.sqrt (T - b))⁻¹ ^ 3 := by positivity
  have hnormalizedVolume : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.metric (1 - sigma)) E := by
    rw [(hG (1 - sigma)).2.2.2.2 E, hseedClock]
    calc
      ENNReal.ofReal V = ENNReal.ofReal ((Real.sqrt (T - b))⁻¹ ^ 3) *
          ENNReal.ofReal (V * Real.sqrt (T - b) ^ 3) := by
        rw [← ENNReal.ofReal_mul hfactorPos.le]
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul_right hvolume _
  have hterminal : b + (T - b) * (1 : ℝ) = T := by ring
  have hball : (G.metric 1).ball x rho = (F.metric T).ball x r := by
    simpa only [rho, hterminal] using (hG 1).2.2.2.1 x r
  have hnormalizedCurv : ∀ s ∈ Icc (1 - rho ^ 2) 1,
      ∀ y ∈ (G.metric 1).ball x rho, (G.connection s).curvatureTensorNorm y ≤ rho⁻¹ ^ 2 := by
    intro s hs y hy
    rw [hball] at hy
    have ht : b + (T - b) * s ∈ Icc (T - r ^ 2) T := by
      constructor <;> nlinarith [hs.1, hs.2]
    rw [(hG s).2.2.1 y]
    calc
      _ ≤ (T - b) * r⁻¹ ^ 2 := mul_le_mul_of_nonneg_left (hcurv _ ht y hy) hd.le
      _ = rho⁻¹ ^ 2 := by
        dsimp only [rho]
        rw [inv_div, div_pow, hsqrt2]
        simp only [inv_pow, div_eq_mul_inv]
  have hbound := PoincareConjecture.M47.seedM15_ordinary_volume hM12 hM13 hM14 hOrdinary U
    (by norm_num : (0 : ℝ) < 1) G x hsigma (by simpa only [sub_zero] using hsigmaOne)
    hsigmaOne.le E hE hnormalizedAccess hnormalizedVolume hrho hrhoAge hnormalizedCurv
  rw [hball, (hG 1).2.2.2.2, hterminal] at hbound
  have hleft : ENNReal.ofReal (U.kappa * rho ^ 3) =
      ENNReal.ofReal ((Real.sqrt (T - b))⁻¹ ^ 3) * ENNReal.ofReal (U.kappa * r ^ 3) := by
    rw [← ENNReal.ofReal_mul hfactorPos.le]
    congr 1
    dsimp only [rho]
    simp only [div_eq_mul_inv, mul_pow]
    ring
  rw [hleft] at hbound
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hfactorPos).ne'
    ENNReal.ofReal_ne_top).mp hbound

end PoincareConjecture.Proofs.M47
