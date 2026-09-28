import PoincareConjecture.Proofs.M47.SeedM15Ordinary
import PoincareConjecture.Proofs.M47.OldRecentSplit
import PoincareConjecture.Statements.M15Noncollapsing










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M47




theorem seedM15_ordinary_radius_volume
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3)
    {taubar l0 V epsilon age : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (hepsilon : 0 < epsilon) (hage : 0 < age)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    {b T tau r : ℝ} (hbt : b < T) (F : RicciFlow 3 M (Icc b T)) (x : M)
    (htauAge : tau < T - b) (htauTop : tau ≤ taubar) (hageTau : age ≤ tau)
    (A : Set M) (hA : IsOpen A)
    (haccess : ∀ q ∈ A, reducedLength F T x q tau ≤ l0)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric (T - tau)) A)
    (hr : 0 < r) (hrepsilon : r ≤ epsilon)
    (hcurv : ∀ s ∈ Icc b T, T - r ^ 2 ≤ s → ∀ q ∈ (F.metric T).ball x r,
      (F.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal ((U.kappa * seedRadiusFactor epsilon age ^ 3) * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  let theta := seedRadiusFactor epsilon age
  have htheta : 0 < theta ∧ theta ≤ 1 := seedRadiusFactor_bounds hepsilon hage
  have hrsmall : 0 < theta * r := mul_pos htheta.1 hr
  have hrle : theta * r ≤ r := mul_le_of_le_one_left hr.le htheta.2
  have hrsq : (theta * r) ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ hrsmall.le hr.le).mpr hrle
  have hrtau : (theta * r) ^ 2 ≤ tau :=
    (seedRadiusFactor_sq_le hepsilon hage hr hrepsilon).trans
      ((half_le_self hage.le).trans hageTau)
  have hballs : (F.metric T).ball x (theta * r) ⊆ (F.metric T).ball x r := by
    intro q hq
    exact hq.trans_le (ENNReal.ofReal_le_ofReal hrle)
  have hcurvSmall : ∀ s ∈ Icc (T - (theta * r) ^ 2) T,
      ∀ q ∈ (F.metric T).ball x (theta * r),
        (F.connection s).curvatureTensorNorm q ≤ (theta * r)⁻¹ ^ 2 := by
    intro s hs q hq
    have hsI : s ∈ Icc b T := ⟨by linarith [hs.1], hs.2⟩
    apply (hcurv s hsI (by linarith [hs.1]) q (hballs hq)).trans
    exact (sq_le_sq₀ (inv_nonneg.mpr hr.le) (inv_nonneg.mpr hrsmall.le)).mpr
      ((inv_le_inv₀ hr hrsmall).mpr hrle)
  exact volume_lower_of_reduced_ball (F.metric T) x hr.le htheta.2
    (seedM15_ordinary_volume hM12 hM13 hM14 hOrdinary U hbt F x
      (hage.trans_le hageTau) htauAge htauTop A hA haccess hvolume hrsmall hrtau hcurvSmall)




theorem exists_seedM15_ordinary_volume_constant
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hM15 : GeneralizedNoncollapsingConclusion.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3)
    {taubar l0 V epsilon age : ℝ}
    (htaubar : 0 < taubar) (hl0 : 0 < l0) (hV : 0 < V)
    (hepsilon : 0 < epsilon) (hage : 0 < age) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
        [CompactSpace M] [ConnectedSpace M]
        (b T tau r : ℝ) (_hbt : b < T) (F : RicciFlow 3 M (Icc b T)) (x : M),
        tau < T - b → tau ≤ taubar → age ≤ tau →
        ∀ A : Set M, IsOpen A →
          (∀ q ∈ A, reducedLength F T x q tau ≤ l0) →
          ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric (T - tau)) A →
          0 < r → r ≤ epsilon →
          (∀ s ∈ Icc b T, T - r ^ 2 ≤ s → ∀ q ∈ (F.metric T).ball x r,
            (F.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2) →
          ENNReal.ofReal (kappa * r ^ 3) ≤
            calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  obtain ⟨U⟩ := hM15.uniform taubar l0 V htaubar hl0 hV
  refine ⟨U.kappa * seedRadiusFactor epsilon age ^ 3,
    seedRadiusFactor_volume_constant_pos hepsilon hage U.kappa_pos, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ b T tau r hbt F x htauAge htauTop hageTau
    A hA haccess hvolume hr hrepsilon hcurv
  exact seedM15_ordinary_radius_volume hM12 hM13 hM14 hOrdinary U hepsilon hage
    hbt F x htauAge htauTop hageTau A hA haccess hvolume hr hrepsilon hcurv

end PoincareConjecture.M47
