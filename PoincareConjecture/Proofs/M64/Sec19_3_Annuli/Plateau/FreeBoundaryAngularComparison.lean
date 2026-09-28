import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryConeReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryHalfDiskComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeMetricEnergy














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

local notation "S" => interior m64AnnulusDomain





theorem lower_halfDisk_angular_energy_comparison {n m N : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {e : M → EuclideanSpace ℝ (Fin m)}
    {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
    {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map S)
    (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hQ : Continuous Q) {bound : ℝ} (hb : ∀ q, ‖Q q‖ ≤ bound)
    (hpos : ∀ q v, 0 ≤ Q q v v) {modulus : ℝ} (hmod : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q modulus ≤ C.annulus.weightedEnergy Q modulus)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (N + 1)))
    (P : EuclideanSpace ℝ (Fin (N + 1)) → M)
    (beta : EuclideanSpace ℝ (Fin (N + 1)) → ℝ)
    {Lip : NNReal} {rho delta eta K p x width epsilon R : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta) (hK : 0 ≤ K) (hk : k ≠ 0)
    (hH : ContDiff ℝ 1 H) (hLip : LipschitzWith Lip H)
    (hHD : ∀ y, ‖fderiv ℝ H y‖ ≤ K)
    (hP : ContMDiffOn (𝓡 (N + 1)) (𝓡 n) 1 P (ball 0 (2 * rho)))
    (hbeta : ContDiffOn ℝ 1 beta (ball 0 (2 * rho)))
    (hPobs : ∀ y ∈ closedBall 0 rho, Robs (e (P y)) = angularPoint (k * beta y))
    (hPD : ∀ y ∈ closedBall 0 rho, ‖fderiv ℝ (e ∘ P) y‖ ≤ K)
    (hcap : ∀ q : M, dist (e q) (e (c0 p)) < delta →
      ‖H (e q)‖ < rho / 4 ∧ P (H (e q)) = q)
    (haxis : ∀ t ∈ Ioo (-eta) eta,
      H (e (c0 (t + p))) = EuclideanSpace.single 0 t ∧
        P (EuclideanSpace.single 0 t) = c0 (t + p))
    (hcurveobs : ∀ t, Robs (e (c0 t)) = angularPoint (k * H0 t))
    (hwindow : ∀ y ∈ Icc (x - width) (x + width),
      A.label0 y - p ∈ Ioo (-eta) eta ∧
        dist (e (c0 (A.label0 y))) (e (c0 p)) < delta / 2)
    (hwidth : 0 < width) (hx : width < x) (hperiod : x + width < curvePeriod)
    (hheight : width < 1) (hepsilon : 0 < epsilon) (hR : R ≤ width) :
    let C := (max modulus modulus⁻¹) ^ 2 * bound * K ^ 4 / 4 * (1 + 4 * Real.pi ^ 2) +
      1 + Real.pi * A.annulus.energy Q / (delta / 2) ^ 2
    0 < C ∧ ∀ᵐ r ∂volume.restrict (Icc epsilon R),
      let angular := fun theta =>
        (-r * Real.sin theta) • A.annulus.column 0 (r • angularPoint theta + annulusPoint x 0) +
        (r * Real.cos theta) • A.annulus.column 1 (r • angularPoint theta + annulusPoint x 0)
      (∫ z in closedBall (annulusPoint x 0) r ∩ S,
        (Q (A.annulus.map z) (A.annulus.column 0 z) (A.annulus.column 0 z) +
          Q (A.annulus.map z) (A.annulus.column 1 z) (A.annulus.column 1 z)) / 2) ≤
        C * ∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2 := by
  let C0 := (max modulus modulus⁻¹) ^ 2 * bound * K ^ 4 / 4 * (1 + 4 * Real.pi ^ 2)
  let C1 := Real.pi * A.annulus.energy Q / (delta / 2) ^ 2
  have hb0 : 0 ≤ bound := (norm_nonneg (Q (A.annulus.map 0))).trans (hb _)
  have hE0 := A.annulus.energy_nonneg Q hpos
  have hden : 0 < (delta / 2) ^ 2 := sq_pos_of_pos (by positivity)
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  have hC1 : 0 ≤ C1 := div_nonneg (mul_nonneg Real.pi_pos.le hE0) hden.le
  refine ⟨?_, ?_⟩
  · change 0 < C0 + 1 + C1
    linarith
  have hdata := A.lower_halfDisk_cone_replacement he hei hA hc0 hc1 hH0 hH1 H P beta
    hrho hdelta hK hk hH hLip hHD hP hbeta hPobs hPD hcap haxis hcurveobs hwindow
    hwidth hx hperiod hheight hepsilon hR
  filter_upwards [hdata, ae_restrict_mem measurableSet_Icc] with r hdata hrI
  let angular := fun theta =>
    (-r * Real.sin theta) • A.annulus.column 0 (r • angularPoint theta + annulusPoint x 0) +
    (r * Real.cos theta) • A.annulus.column 1 (r • angularPoint theta + annulusPoint x 0)
  let E := ∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2
  change _ ≤ (C0 + 1 + C1) * E
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hr : 0 < r := hepsilon.trans_le hrI.1
  have hrW : r ≤ width := hrI.2.trans hR
  by_cases hsmall : Real.pi * E < (delta / 2) ^ 2
  · obtain ⟨sigma, f, V, u, W, hsc, hsm, hsp, hsn, hout,
      hf, hV, hu, hW, ht, ho, hg, hp, hcone⟩ := hdata hsmall
    have hcomp := A.local_energy_le_of_halfDisk_data Q hQ hei.isEmbedding hb hpos hmod
      hminimum hc0 hc1 hH0 hH1 hr.le (hrW.trans_lt hx) (by linarith) (hrW.trans_lt hheight)
      sigma hsc hsm hsp hsn hout f V u W hf hV hu hW ht ho hg hp
    have hmetric := m64Observed_replacement_energy_le_norm e hei.isEmbedding Q hQ hb f V hf hV
    have hlocal := hcomp.trans (mul_le_mul_of_nonneg_left
      (hmetric.trans (mul_le_mul_of_nonneg_left hcone (by positivity))) (sq_nonneg _))
    have hlocal' : (∫ z in closedBall (annulusPoint x 0) r ∩ S,
        (Q (A.annulus.map z) (A.annulus.column 0 z) (A.annulus.column 0 z) +
          Q (A.annulus.map z) (A.annulus.column 1 z) (A.annulus.column 1 z)) / 2) ≤ C0 * E := by
      apply hlocal.trans_eq
      dsimp only [C0, E, angular]
      ring
    exact hlocal'.trans (mul_le_mul_of_nonneg_right (by linarith) hE)
  · have htotal : (∫ z in closedBall (annulusPoint x 0) r ∩ S,
        (Q (A.annulus.map z) (A.annulus.column 0 z) (A.annulus.column 0 z) +
          Q (A.annulus.map z) (A.annulus.column 1 z) (A.annulus.column 1 z)) / 2) ≤
        A.annulus.energy Q :=
      setIntegral_mono_set (A.annulus.energy_integrable Q hQ hei.isEmbedding hb)
        (ae_of_all _ fun z => div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num))
        (ae_of_all _ fun _ hz => hz.2)
    have hlarge : A.annulus.energy Q ≤ C1 * E := by
      dsimp only [C1]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hden).mpr
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hsmall) hE0
      nlinarith
    exact (htotal.trans hlarge).trans (mul_le_mul_of_nonneg_right (by linarith) hE)

end PoincareConjecture.M64FreeWeakPhaseAnnulus
