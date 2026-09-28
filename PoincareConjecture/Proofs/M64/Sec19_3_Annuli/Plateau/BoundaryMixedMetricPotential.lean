import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedPotential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryComponentPairings












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64MixedMetric_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64MixedMetric_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64MixedMetric_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64MixedMetric_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1200000 in





theorem m64WeightedMixedMetric_potential
    (dirichlet : Fin n → Prop) {O S : Set LoopPlane} (hO : IsOpen O) (hS : MeasurableSet S)
    (G : LoopPlane → E →L[ℝ] E →L[ℝ] ℝ)
    (T : LoopPlane → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (w : Fin 2 → ℝ) (V du : Fin 2 → LoopPlane → E) (u : LoopPlane → E)
    {kappa mu C Lambda delta : ℝ}
    (hk : 0 < kappa) (hmu : 0 < mu) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda)
    (hsmall : C * Lambda * delta ≤ (kappa * mu) / 4)
    (hG : ∀ p ∈ S, ‖G p‖ ≤ C ∧ ‖T p‖ ≤ C ∧
      ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G p v v)
    (hu : Continuous u)
    (hz : ∀ j, dirichlet j → ∀ p : LoopPlane, p 1 < 0 → u p j = 0)
    (hub : ∀ p ∈ S, ‖u p‖ ≤ delta)
    (hdu : ∀ i, MemLp (du i) 2 volume)
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun p => du i p j) (fun p => u p j) univ)
    (hcolumns : ∀ p ∈ S, ∀ i, du i p = V i p)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict S))
    (hflux : ∀ j : Fin n, ∀ i : Fin 2,
      MemLp (fun p => w i * G p (V i p) (EuclideanSpace.single j 1))
        2 (volume.restrict S))
    (hsource : ∀ j : Fin n, IntegrableOn (fun p =>
      -(∑ i : Fin 2, w i * T p (EuclideanSpace.single j 1) (V i p) (V i p)) / 2) S)
    (heq : ∀ j : Fin n, ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ O →
      (dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2,
        S.indicator (fun q => w i * G q (V i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, S.indicator (fun q => -(∑ i : Fin 2,
          w i * T q (EuclideanSpace.single j 1) (V i q) (V i q)) / 2) p * phi p)
    {xi : LoopPlane → ℝ} (hxi : ContDiff ℝ ∞ xi) (hc : HasCompactSupport xi)
    (hs : tsupport xi ⊆ O) :
    (kappa * mu) / 2 * (∫ p in S, (∑ i : Fin 2, ‖V i p‖ ^ 2) * xi p ^ 2) ≤
      (4 * (C * Lambda) ^ 2 * delta ^ 2 / (kappa * mu)) *
        ∫ p in S, ∑ i : Fin 2, (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2 := by
  classical
  let F := fun (j : Fin n) (i : Fin 2) =>
    S.indicator (fun p => w i * G p (V i p) (EuclideanSpace.single j 1))
  let b := fun j : Fin n => S.indicator (fun p =>
    -(∑ i : Fin 2, w i * T p (EuclideanSpace.single j 1) (V i p) (V i p)) / 2)
  let H := S.indicator (fun p => ∑ i : Fin 2, ‖V i p‖ ^ 2)
  let W := S.indicator (fun _ : LoopPlane => (1 : ℝ))
  have hL : 0 ≤ Lambda := hmu.le.trans ((hw 0).1.trans (hw 0).2)
  have hw0 (i : Fin 2) : 0 ≤ w i ∧ w i ≤ Lambda :=
    ⟨hmu.le.trans (hw i).1, (hw i).2⟩
  have hHp (p : LoopPlane) : 0 ≤ H p := indicator_nonneg
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) p
  have hFM (j : Fin n) (i : Fin 2) : MemLp (F j i) 2 volume :=
    (memLp_indicator_iff_restrict hS).mpr (hflux j i)
  have hbI (j : Fin n) : Integrable (b j) :=
    (integrable_indicator_iff hS).mpr (hsource j)
  have hprincipal (p : LoopPlane) : kappa * mu * H p - 0 ≤
      ∑ j : Fin n, ∑ i : Fin 2, F j i p * du i p j := by
    by_cases hp : p ∈ S
    · simp only [F, H, indicator_of_mem hp, hcolumns p hp, sub_zero]
      have hpair := m64WeightedBoundary_principal_pairing (G p) w
        (fun i => V i p) (fun _ => (0 : E))
      simp only [sub_zero] at hpair
      rw [hpair, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      calc
        kappa * mu * ‖V i p‖ ^ 2 = mu * (kappa * ‖V i p‖ ^ 2) := by ring
        _ ≤ w i * (kappa * ‖V i p‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hw i).1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left ((hG p hp).2.2 _) (hw0 i).1
    · simp only [F, H, indicator_of_notMem hp, mul_zero, zero_mul, sub_zero,
        Finset.sum_const_zero, le_refl]
  have hsrc (p : LoopPlane) : (∑ j : Fin n, b j p * u p j) ≤ C * Lambda * delta * H p := by
    by_cases hp : p ∈ S
    · simp only [b, H, indicator_of_mem hp]
      rw [m64WeightedBoundary_source_pairing]
      have hsum : 0 ≤ ∑ i : Fin 2, ‖V i p‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc
        _ ≤ |-(∑ i : Fin 2, w i * T p (u p) (V i p) (V i p)) / 2| := le_abs_self _
        _ ≤ C * Lambda * ‖u p‖ * (∑ i : Fin 2, ‖V i p‖ ^ 2) / 2 :=
          m64WeightedBoundary_source_bound (T p) w (fun i => V i p) (u p) (hG p hp).2.1 hw0
        _ ≤ C * Lambda * delta * (∑ i : Fin 2, ‖V i p‖ ^ 2) / 2 := by
          gcongr
          exact hub p hp
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC hL) hdelta]
    · simp only [b, H, indicator_of_notMem hp, zero_mul, mul_zero,
        Finset.sum_const_zero, le_refl]
  have hcross (p : LoopPlane) : (∑ j : Fin n, ∑ i : Fin 2, F j i p * u p j *
      fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2 ≤
      (C * Lambda) ^ 2 * delta ^ 2 * H p * W p *
        ∑ i : Fin 2, (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2 := by
    by_cases hp : p ∈ S
    · simp only [F, H, W, indicator_of_mem hp, mul_one]
      rw [m64WeightedBoundary_cross_pairing]
      apply (m64WeightedBoundary_cross_bound (G p) w (fun i => V i p) (u p)
        (fun i => fderiv ℝ xi p (EuclideanSpace.single i 1)) (hG p hp).1 hw0).trans
      rw [mul_pow]
      gcongr
      exact hub p hp
    · simp only [F, H, indicator_of_notMem hp, zero_mul, mul_zero,
        Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0), le_refl]
  have hHI : Integrable H := by
    apply (integrable_indicator_iff hS).mpr
    exact integrable_finsetSum _ fun i _ => by
      simpa only [pow_two, Pi.mul_apply] using! (hV i).norm.integrable_mul (hV i).norm
  have hxic : HasCompactSupport (fun p => xi p ^ 2) :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) xi)
  have hHxi : Integrable (fun p => H p * xi p ^ 2) := memLp_one_iff_integrable.mp
    (((hxi.continuous.pow 2).memLp_of_hasCompactSupport hxic : MemLp _ ⊤ volume).mul'
      (memLp_one_iff_integrable.mpr hHI))
  have hgrad : Integrable (fun p =>
      ∑ i : Fin 2, (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2) := by
    apply integrable_finsetSum _ fun i _ => ?_
    have hd : MemLp (fun p => fderiv ℝ xi p (EuclideanSpace.single i 1)) 2 volume :=
      ((hxi.continuous_fderiv (by simp)).clm_apply continuous_const
        ).memLp_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) _)
    simpa only [pow_two, Pi.mul_apply] using! hd.integrable_mul hd
  have hWeq : (fun p => W p * ∑ i : Fin 2,
      (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2) =
      S.indicator (fun p => ∑ i : Fin 2,
        (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2) := by
    funext p
    by_cases hp : p ∈ S <;> simp [W, hp]
  have hbound := m64NaturalGrowth_mixed_potential_bound dirichlet hO
    (mul_pos hk hmu) hsmall hHp
    (fun p => indicator_nonneg (fun _ _ => zero_le_one) p) hFM hbI
    (fun j => (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hu)
    (fun j i => (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (hdu i))
    (fun j i => hweak i j) hz hxi hc hs heq hprincipal hsrc hcross hHxi
    (by rw [hWeq]; exact (integrable_indicator_iff hS).mpr hgrad.integrableOn)
  have hHeq : (∫ p, H p * xi p ^ 2) =
      ∫ p in S, (∑ i : Fin 2, ‖V i p‖ ^ 2) * xi p ^ 2 := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : p ∈ S <;> simp [H, hp]
  rw [hHeq, hWeq, integral_indicator hS] at hbound
  simpa only [zero_mul, zero_add] using hbound

end PoincareConjecture
