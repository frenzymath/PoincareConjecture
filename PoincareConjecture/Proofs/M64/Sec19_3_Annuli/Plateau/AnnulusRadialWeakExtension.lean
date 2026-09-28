import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialTests

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "v" => m64AnnulusRadialTranslation

namespace M64ObservedWeakAnnulus

def lowerExtensionMap (A : M64ObservedWeakAnnulus (n := n) e c0 c1) : LoopPlane → M :=
  m64AnnulusLowerExtend (fun p => c0 (p 0)) A.map

def lowerExtensionColumn (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) :
    LoopPlane → E :=
  m64AnnulusLowerExtend
    (fun p => fderiv ℝ (fun q : LoopPlane => e (c0 (q 0))) p (EuclideanSpace.single i 1))
    (A.column i)

theorem lower_extension_memLp
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (hc0 : ContDiff ℝ 1 (e ∘ c0)) :
    MemLp (e ∘ A.lowerExtensionMap) 2 (volume.restrict O) ∧
      ∀ i, MemLp (A.lowerExtensionColumn i) 2 (volume.restrict O) := by
  have hC : ContDiff ℝ 1 (fun p : LoopPlane => e (c0 (p 0))) := by
    simpa only [Function.comp_def] using m64BoundaryCurvePlane_contDiff hc0
  constructor
  · unfold lowerExtensionMap
    rw [m64AnnulusLowerExtend_comp]
    exact m64AnnulusLowerExtend_memLp (m64Annulus_continuous_memLp_two hC.continuous)
      A.observed_memLp
  · intro i
    exact m64AnnulusLowerExtend_memLp
      (m64Annulus_continuous_memLp_two
        ((hC.continuous_fderiv (by simp)).clm_apply continuous_const)) (Lp.memLp (A.column i))

theorem lower_original_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in S, phi p • A.column i p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p)) =
      if i = 1 then -(∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 0) • e (c0 x)) else 0 := by
  obtain ⟨htop, -, hleft, hright⟩ := m64LowerTest_boundary_zero hs
  fin_cases i
  · exact A.seam phi hp (fun s _ => by rw [hright, hleft])
  · change (∫ p in S, phi p • A.column 1 p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • e (A.map p)) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) • e (c0 x))
    rw [A.boundary phi hp]
    calc
      _ = ∫ x in Icc (0 : ℝ) curvePeriod, -(phi (annulusPoint x 0) • e (c0 x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [htop, zero_smul, zero_sub]
      _ = _ := integral_neg _

theorem lower_extension_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (hc0 : ContDiff ℝ 1 (e ∘ c0))
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in O, phi p • A.lowerExtensionColumn i p) +
      (∫ p in O, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.lowerExtensionMap p)) = 0 := by
  let C : LoopPlane → E := fun p => e (c0 (p 0))
  let D : LoopPlane → E := fun p => fderiv ℝ C p (EuclideanSpace.single i 1)
  let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hC : ContDiff ℝ 1 C := by
    simpa only [Function.comp_def] using m64BoundaryCurvePlane_contDiff hc0
  have hCM := m64Annulus_continuous_memLp_two hC.continuous
  have hDM : MemLp D 2 (volume.restrict S) := m64Annulus_continuous_memLp_two
    ((hC.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hpM : MemLp phi 2 (volume.restrict O) :=
    (hp.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdM : MemLp dphi 2 (volume.restrict O) :=
    (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  have hvalue (p : LoopPlane) : e (A.lowerExtensionMap p) =
      m64AnnulusLowerExtend C (fun q => e (A.map q)) p :=
    congrFun (m64AnnulusLowerExtend_comp (fun q => c0 (q 0)) A.map e) p
  have hobs : MemLp (fun p => e (A.map p)) 2 (volume.restrict S) := A.observed_memLp
  simp_rw [hvalue]
  change (∫ p in O, phi p • m64AnnulusLowerExtend D (A.column i) p) +
    (∫ p in O, dphi p • m64AnnulusLowerExtend C (fun q => e (A.map q)) p) = 0
  rw [m64AnnulusLowerExtend_integral_smul hDM (Lp.memLp (A.column i)) hpM,
    m64AnnulusLowerExtend_integral_smul hCM hobs hdM]
  have htop := A.lower_original_green hp hs i
  have hbottom := m64Annulus_lower_boundaryCurve_green hc0 hp hs i
  change (∫ p in S, phi (p - v) • D p) + (∫ p in S, dphi (p - v) • C p) =
    if i = 1 then ∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) • e (c0 x) else 0
    at hbottom
  calc
    _ = ((∫ p in S, phi p • A.column i p) + ∫ p in S, dphi p • e (A.map p)) +
        ((∫ p in S, phi (p - v) • D p) + ∫ p in S, dphi (p - v) • C p) := by abel
    _ = 0 := by rw [htop, hbottom]; split_ifs <;> abel

theorem lower_extension_weak_partial
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (i : Fin 2) (b : Fin m) :
    HasWeakPartialDeriv i (fun p => A.lowerExtensionColumn i p b)
      (fun p => e (A.lowerExtensionMap p) b) O := by
  intro phi hp hc hs
  have hpM : MemLp phi 2 (volume.restrict O) :=
    (hp.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdM : MemLp (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
    (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  let L := EuclideanSpace.proj (𝕜 := ℝ) b
  have hproj (f : LoopPlane → E) (hf : MemLp f 2 (volume.restrict O))
      (psi : LoopPlane → ℝ) (hpsi : MemLp psi 2 (volume.restrict O)) :
      L (∫ p in O, psi p • f p) = ∫ p in O, psi p * f p b := by
    simpa only [map_smul, smul_eq_mul, L, EuclideanSpace.coe_proj] using
      (L.integral_comp_comm (m64L2_test_integrable hf hpsi)).symm
  have h := congrArg L (A.lower_extension_green hc0 (hp.of_le (by simp)) hc hs i)
  have hobs : MemLp (fun p => e (A.lowerExtensionMap p)) 2 (volume.restrict O) :=
    (A.lower_extension_memLp hc0).1
  simp only [map_add, map_zero] at h
  rw [hproj _ ((A.lower_extension_memLp hc0).2 i) _ hpM,
    hproj _ hobs _ hdM] at h
  simp only [mul_comm] at h ⊢
  linarith

end M64ObservedWeakAnnulus

end PoincareConjecture
