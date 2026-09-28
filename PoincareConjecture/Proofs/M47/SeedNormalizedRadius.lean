import PoincareConjecture.Proofs.M47.SeedNormalizedM15
import PoincareConjecture.Proofs.M47.OldRecentSplit









set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem seedM15_normalized_radius_volume
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
    (htauAge : tau < T - b) (hlo : 3 * (T - b) / 4 ≤ tau)
    (E : Set M) (hE : IsOpen E)
    (haccess : ∀ y ∈ E, reducedLength F T x y tau ≤ l0)
    (hvolume : ENNReal.ofReal (V * Real.sqrt (T - b) ^ 3) ≤
      calibratedMetricVolume (F.metric (T - tau)) E)
    (hr : 0 < r) (hsize : r ^ 2 ≤ 8 * (T - b))
    (hcurv : ∀ s ∈ Icc b T, T - r ^ 2 ≤ s → ∀ y ∈ (F.metric T).ball x r,
      (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal ((U.kappa / 64) * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  have hd : 0 < T - b := sub_pos.mpr hbt
  have hrsmall : 0 < r / 4 := div_pos hr (by norm_num)
  have hrtau : (r / 4) ^ 2 ≤ tau := by nlinarith
  have hballs : (F.metric T).ball x (r / 4) ⊆ (F.metric T).ball x r := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hsmallCurv : ∀ s ∈ Icc (T - (r / 4) ^ 2) T,
      ∀ y ∈ (F.metric T).ball x (r / 4),
        (F.connection s).curvatureTensorNorm y ≤ (r / 4)⁻¹ ^ 2 := by
    intro s hs y hy
    have hsI : s ∈ Icc b T := ⟨by linarith [hs.1], hs.2⟩
    apply (hcurv s hsI (by nlinarith [hs.1]) y (hballs hy)).trans
    apply (sq_le_sq₀ (inv_nonneg.mpr hr.le) (inv_nonneg.mpr hrsmall.le)).mpr
    exact (inv_le_inv₀ hr hrsmall).mpr (by linarith)
  have hv := seedM15_normalized_history_volume hM12 hM13 hM14 hOrdinary U hbt F x
    (by linarith) htauAge E hE haccess hvolume hrsmall hrtau hsmallCurv
  have hv' := volume_lower_of_reduced_ball (F.metric T) x (kappa := U.kappa) hr.le
    (by norm_num : (1 / 4 : ℝ) ≤ 1)
    (by simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using hv)
  convert hv' using 1
  congr 1
  ring

end PoincareConjecture.Proofs.M47
