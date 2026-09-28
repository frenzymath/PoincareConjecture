import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusEnergyIdentity
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness




theorem m64WeakPartial_eq_fderiv_of_contDiffOn {O : Set LoopPlane} (hO : IsOpen O)
    {u W : LoopPlane → ℝ} {i : Fin 2} (hu : ContDiffOn ℝ 1 u O)
    (hW : MemLp W 2 (volume.restrict O)) (hw : HasWeakPartialDeriv i W u O) :
    W =ᵐ[volume.restrict O] (fun p => fderiv ℝ u p (EuclideanSpace.single i 1)) := by
  let D := fun p => fderiv ℝ u p (EuclideanSpace.single i 1)
  have hDc : ContinuousOn D O :=
    (hu.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have hloc : LocallyIntegrableOn (fun p => W p - D p) O volume :=
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hW.locallyIntegrable (by norm_num))).sub
      (hDc.locallyIntegrableOn hO.measurableSet)
  have hzero := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hO.measurableSet] with p hp hpO
    exact sub_eq_zero.mp (hp hpO)
  intro phi hp hc hs
  have hpM := (hp.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc
    ).mono_measure (Measure.restrict_le_self (s := O))
  have hWi : Integrable (fun p => phi p * W p) (volume.restrict O) := by
    have h := hpM.integrable_mul hW
    change Integrable (fun p => phi p * W p) (volume.restrict O) at h
    exact h
  have hDi : Integrable (fun p => phi p * D p) (volume.restrict O) := by
    have h := (integrable_test_smul hO hp.continuous hc hs hDc).integrableOn (s := O)
    change Integrable (fun p => phi p * D p) (volume.restrict O) at h
    exact h
  have hclass := setIntegral_test_fderiv hO hu hp hc hs (EuclideanSpace.single i 1)
  have hweak := hw phi hp hc hs
  have houtside (p : LoopPlane) (hpO : p ∉ O) : phi p * (W p - D p) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun hpS => hpO (hs hpS)), zero_mul]
  change (∫ p, phi p * (W p - D p)) = 0
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
  simp_rw [mul_sub]
  rw [integral_sub hWi hDi]
  change (∫ p in O, u p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
    -(∫ p in O, W p * phi p) at hweak
  rw [show (∫ p in O, u p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      ∫ p in O, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p from
        integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _),
    show (∫ p in O, W p * phi p) = ∫ p in O, phi p * W p from
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)] at hweak
  change (∫ p in O, phi p * D p) =
    -(∫ p in O, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) at hclass
  linarith




theorem m64WeakColumns_eq_fderiv_of_contDiffOn {m : ℕ} {O : Set LoopPlane}
    (hO : IsOpen O) {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)}
    (hu : ContDiffOn ℝ 1 u O) (hW : ∀ i, MemLp (W i) 2 (volume.restrict O))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) O) :
    ∀ i, W i =ᵐ[volume.restrict O] (fun p => fderiv ℝ u p (EuclideanSpace.single i 1)) := by
  intro i
  have hcoord (j : Fin m) : (fun p => W i p j) =ᵐ[volume.restrict O]
      (fun p => (fderiv ℝ u p (EuclideanSpace.single i 1)) j) := by
    let P := EuclideanSpace.proj (𝕜 := ℝ) j
    have h := m64WeakPartial_eq_fderiv_of_contDiffOn hO
      (P.contDiff.comp_contDiffOn hu) (P.comp_memLp' (hW i)) (hw i j)
    filter_upwards [h, ae_restrict_mem hO.measurableSet] with p hp hpO
    change P (W i p) = fderiv ℝ (P ∘ u) p (EuclideanSpace.single i 1) at hp
    change P (W i p) = P (fderiv ℝ u p (EuclideanSpace.single i 1))
    rw [hp, fderiv_comp p P.differentiableAt
      ((hu.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp)), P.fderiv]
    rfl
  filter_upwards [ae_all_iff.mpr hcoord] with p hp
  exact PiLp.ext hp

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

omit [IsManifold (𝓡 n) ∞ M] in



theorem M64ObservedWeakAnnulus.classical_columns_of_contMDiffOn
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) :
    ∀ i, (A.column i : LoopPlane → E) =ᵐ[volume.restrict S]
      (fun p => fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1)) := by
  have hu : ContDiffOn ℝ 1 (e ∘ A.map) S := by
    intro p hp
    exact (contMDiffAt_iff_contDiffAt.mp ((he _).comp p
      (hA.contMDiffAt (isOpen_interior.mem_nhds hp)))).contDiffWithinAt
  exact m64WeakColumns_eq_fderiv_of_contDiffOn isOpen_interior hu
    (fun i => Lp.memLp (A.column i)) A.weak_partial




theorem M64ObservedWeakAnnulus.energyDensity_eq_ae_of_contMDiffOn
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) :
    (fun p => (Q (A.map p) (A.column 0 p) (A.column 0 p) +
      Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2) =ᵐ[volume.restrict S]
        m60EnergyDensity g A.map := by
  have hcol := A.classical_columns_of_contMDiffOn he hA
  filter_upwards [hcol 0, hcol 1, ae_restrict_mem isOpen_interior.measurableSet]
    with p h0 h1 hp
  rw [h0, h1]
  have hd := (hA.contMDiffAt (isOpen_interior.mem_nhds hp)).mdifferentiableAt (by simp)
  rw [m64ObservedMetric_diagonal_of_mDifferentiableAt g e he Q hdiag hd 0,
    m64ObservedMetric_diagonal_of_mDifferentiableAt g e he Q hdiag hd 1]
  simp only [m60EnergyDensity, Matrix.trace_fin_two]
  ring




theorem M64ObservedWeakAnnulus.energy_eq_integral_of_contMDiffOn
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) :
    A.energy Q = ∫ p in S, m60EnergyDensity g A.map p :=
  integral_congr_ae (A.energyDensity_eq_ae_of_contMDiffOn g he Q hdiag hA)

end PoincareConjecture
