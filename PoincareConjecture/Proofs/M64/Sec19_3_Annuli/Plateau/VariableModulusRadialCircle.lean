import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusRadialReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialCircleComparison












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

set_option maxHeartbeats 1000000 in




theorem M64ObservedWeakAnnulus.weighted_lower_circle_energy_comparison
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0) (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ W.weightedEnergy Q modulus) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (a : LoopPlane), a 1 = 0 → ∀ (rho : ℝ), 0 < rho → rho ≤ rho0 →
        closedBall a rho ⊆ O → ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
          A.lowerDiskEnergy Q a (rho * Real.exp (-s)) ≤
            C * (A.lowerAngularEnergy a rho s + rho ^ 2) := by
  obtain ⟨epsilon, hepsilon, rho0, hrho0, C0, hC0, hfill⟩ :=
    m64ChartReadable_small_radial_H1_filling_energy g e he hei.isEmbedding hread
      c0 hc0 hc0P Q hQ
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨K, hK⟩ := hbounded.exists_norm_le
  have hbound (q : M) : ‖Q q‖ ≤ K := hK _ (mem_range_self q)
  have hE := A.lowerTotalEnergy_nonneg Q hpos
  let D := (max modulus modulus⁻¹) ^ 2
  have hD : 0 ≤ D := sq_nonneg _
  let C := D * C0 + A.lowerTotalEnergy Q / epsilon + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCC : D * C0 ≤ C := by dsimp [C]; linarith [div_nonneg hE hepsilon.le]
  have hEC : A.lowerTotalEnergy Q / epsilon ≤ C := by
    dsimp [C]; linarith [mul_nonneg hD hC0]
  refine ⟨rho0, hrho0, C, hC, ?_⟩
  intro a ha rho hrho hrrho0 hKO
  obtain ⟨hu0, hV0, hw0, -⟩ := A.lower_extension_data he hc0
  have hcircles := A.lower_local_circle_traces he hei hc0 a hrho hKO
  have hgreens := m64WeakMap_local_circle_green m64AnnulusLowerDomain_isOpen a hrho hKO
    (e ∘ A.lowerExtensionMap) A.lowerExtensionColumn hu0 hV0 hw0
  filter_upwards [hcircles, hgreens, ae_restrict_mem measurableSet_Icc] with s hcircle hgreen hs
  let r := rho * Real.exp (-s)
  let v := fun x => m64MorreyPolarAngularColumn a rho A.lowerExtensionColumn (annulusPoint x s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hrrho : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))
  have hball : ball a r ⊆ O :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hrrho).trans hKO)
  have hang : 0 ≤ A.lowerAngularEnergy a rho s := A.lowerAngularEnergy_nonneg a rho s
  by_cases hsmall : A.lowerAngularEnergy a rho s < epsilon
  · obtain ⟨gamma, w, hgc, hgp, hga, hv, -, -, hw, hwp, huni, hder⟩ := hcircle
    have hvp : Function.Periodic v curvePeriod :=
      m64MorreyPolarAngularColumn_periodic a rho A.lowerExtensionColumn s
    have hUp : Function.Periodic (e ∘ gamma) curvePeriod :=
      fun x => congrArg e (hgp x)
    obtain ⟨hva, hunia, hdera, hFTCa, hEshift⟩ :=
      m64Periodic_H1_shift w hw hwp (e ∘ gamma) v hUp hvp hv huni hder Real.pi
    have hwa (j : ℕ) : ContDiff ℝ 1 (fun x => w j (x + Real.pi)) :=
      (hw j).comp (contDiff_id.add contDiff_const)
    have hshiftSmall : (∫ x in Icc (0 : ℝ) curvePeriod, ‖v (x + Real.pi)‖ ^ 2) < epsilon := by
      rw [hEshift]
      exact hsmall
    have hfixedTrace := A.lower_circle_fixed_shift hei hc0.continuous hgc hgp ha hr hga
    obtain ⟨F, W, hFc, hcircleF, hfixedF, huF, htF, hwF, hFE⟩ :=
      hfill a r hr (hrrho.trans hrrho0) (fun x => gamma (x + Real.pi))
        (hgc.comp (continuous_id.add continuous_const)) (hgp.add_const Real.pi) hfixedTrace
        (fun j x => w j (x + Real.pi)) hwa (fun j => (hwp j).add_const Real.pi)
        hunia (fun x => v (x + Real.pi)) hva
        (by simpa +instances only [Function.comp_def, zero_add] using! hFTCa) hdera hshiftSmall
    let f := F ∘ m64ConeNormalize a r
    let V := fun i p => r⁻¹ • W i (m64ConeNormalize a r p)
    obtain ⟨-, huf, hV, ht, hweak⟩ := m64RadialDisk_affine_data e F
      (fun i z => W i z) hFc huF (fun i => Lp.memLp (W i)) htF hwF a hr
    have hfixed (p : LoopPlane) (hp : p ∈ ball a r) (hpy : p 1 < 0) : f p = c0 (p 0) := by
      have hz : m64ConeNormalize a r p ∈ closedBall 0 1 := by
        change p ∈ m64ConeNormalize a r ⁻¹' closedBall 0 1
        rw [m64ConeNormalize_preimage_closedBall a hr]
        exact ball_subset_closedBall hp
      have hback : a + r • m64ConeNormalize a r p = p := by
        rw [m64ConeNormalize, smul_inv_smul₀ hr.ne']
        abel
      change F (m64ConeNormalize a r p) = _
      rw [hfixedF _ hz (m64ConeNormalize_lower ha hr hpy.le), hback]
    have hmatching (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
        (∫ p in ball a r, phi p • V i p) +
          (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
        (∫ p in ball a r, phi p • A.lowerExtensionColumn i p) +
          (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
            e (A.lowerExtensionMap p)) := by
      have hFgreen := m64RadialDisk_affine_green (e ∘ F) (fun i z => W i z)
        huF (fun i => Lp.memLp (W i)) hwF (he.continuous.comp_continuousOn hFc) a hr phi hphi i
      simp only [Function.comp_apply, hcircleF] at hFgreen
      rw [m64CircleIntegral_shift] at hFgreen
      simp only [sub_add_cancel] at hFgreen
      have hAgreen := hgreen phi hphi i
      have hnull := M60.haar_ball_ae_eq_closedBall volume a r
      rw [← setIntegral_congr_set hnull, ← setIntegral_congr_set hnull] at hAgreen
      refine hFgreen.trans ((congrArg (fun z => r • z) (integral_congr_ae ?_)).trans
        hAgreen.symm)
      filter_upwards [hga] with x hx
      change gamma x = A.lowerExtensionMap (a + r • angularPoint (x - Real.pi)) at hx
      rw [hx]
      rfl
    have hlocal := A.weighted_lower_local_energy_le_of_matching_flux hce Q hQ
      hei.isEmbedding hbound hpos hmodulus hmin a r hball f V huf hV ht hweak hfixed hmatching
    dsimp only [f, V, Function.comp_apply] at hlocal
    rw [m64RadialDisk_affine_energy F (fun i z => W i z) a hr Q] at hlocal
    have hFE' : (∫ z in ball (0 : LoopPlane) 1,
        (Q (F z) (W 0 z) (W 0 z) + Q (F z) (W 1 z) (W 1 z)) / 2) ≤
        C0 * (A.lowerAngularEnergy a rho s + r ^ 2) := by
      simpa +instances only [hEshift, M64ObservedWeakAnnulus.lowerAngularEnergy, v] using! hFE
    calc
      _ ≤ D * (C0 * (A.lowerAngularEnergy a rho s + r ^ 2)) :=
        hlocal.trans (mul_le_mul_of_nonneg_left hFE' hD)
      _ = D * C0 * (A.lowerAngularEnergy a rho s + r ^ 2) := by ring
      _ ≤ D * C0 * (A.lowerAngularEnergy a rho s + rho ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          ((sq_le_sq₀ hr.le hrho.le).mpr hrrho)) (mul_nonneg hD hC0)
      _ ≤ C * (A.lowerAngularEnergy a rho s + rho ^ 2) :=
        mul_le_mul_of_nonneg_right hCC (add_nonneg hang (sq_nonneg rho))
  · have hlarge : epsilon ≤ A.lowerAngularEnergy a rho s := le_of_not_gt hsmall
    calc
      _ ≤ A.lowerTotalEnergy Q := A.lowerDiskEnergy_le_total hce Q hQ hei.isEmbedding
        hbound hpos a r hball
      _ = (A.lowerTotalEnergy Q / epsilon) * epsilon := (div_mul_cancel₀ _ hepsilon.ne').symm
      _ ≤ (A.lowerTotalEnergy Q / epsilon) * A.lowerAngularEnergy a rho s :=
        mul_le_mul_of_nonneg_left hlarge (div_nonneg hE hepsilon.le)
      _ ≤ C * A.lowerAngularEnergy a rho s := mul_le_mul_of_nonneg_right hEC hang
      _ ≤ C * (A.lowerAngularEnergy a rho s + rho ^ 2) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg rho)) hC.le

end PoincareConjecture
