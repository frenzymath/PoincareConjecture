import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialTests
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "T" => m64AnnulusRadialFlip
local notation "v" => m64AnnulusRadialTranslation
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)




def lowerReflectedValue (A : M64ObservedWeakAnnulus (n := n) e c0 c1) : LoopPlane → E :=
  m64AnnulusLowerExtend ((e ∘ A.map) ∘ T) (e ∘ A.map)



def lowerReflectedColumn (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) :
    LoopPlane → E := m64AnnulusLowerExtend
  (fun p => (if i = 0 then (1 : ℝ) else -1) • A.column i (T p)) (A.column i)



theorem lower_reflected_memLp (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    MemLp A.lowerReflectedValue 2 (volume.restrict O) ∧
      ∀ i, MemLp (A.lowerReflectedColumn i) 2 (volume.restrict O) := by
  refine ⟨m64AnnulusLowerExtend_memLp
    (A.observed_memLp.comp_measurePreserving m64AnnulusRadialFlip_restrict_measurePreserving)
    A.observed_memLp, ?_⟩
  intro i
  exact m64AnnulusLowerExtend_memLp
    (by simpa +instances only [Pi.smul_apply, Function.comp_apply] using!
      ((Lp.memLp (A.column i)).comp_measurePreserving
        m64AnnulusRadialFlip_restrict_measurePreserving).const_smul
          (if i = 0 then (1 : ℝ) else -1)) (Lp.memLp (A.column i))

private theorem observed_lower_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (ht : ∀ x, phi (annulusPoint x 1) = 0)
    (hl : ∀ s, phi (annulusPoint 0 s) = 0)
    (hr : ∀ s, phi (annulusPoint curvePeriod s) = 0) (i : Fin 2) :
    (∫ p in S, phi p • A.column i p) +
      (∫ p in S, fderiv ℝ phi p (ei i) • e (A.map p)) =
      if i = 1 then -(∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 0) • e (c0 x)) else 0 := by
  fin_cases i
  · exact A.seam phi hp (fun s _ => by rw [hl, hr])
  · simpa [ht, integral_neg] using A.boundary phi hp




theorem lower_reflected_green (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in O, phi p • A.lowerReflectedColumn i p) +
      (∫ p in O, fderiv ℝ phi p (ei i) • A.lowerReflectedValue p) = 0 := by
  let dphi := fun p => fderiv ℝ phi p (ei i)
  let psi := fun p => phi (p - v)
  have hpsi : ContDiff ℝ 1 psi := hp.comp (contDiff_id.sub contDiff_const)
  have hder (p : LoopPlane) : fderiv ℝ psi p (ei i) = dphi (p - v) :=
    m64FDeriv_sub_translation hp v p (ei i)
  obtain ⟨htop, hbottom, hleft, hright⟩ := m64LowerTest_boundary_zero hs
  have hpM : MemLp phi 2 (volume.restrict O) :=
    (hp.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdM : MemLp dphi 2 (volume.restrict O) :=
    (((hp.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  have hF := A.observed_memLp.comp_measurePreserving
    m64AnnulusRadialFlip_restrict_measurePreserving
  have hW : MemLp (fun p => (if i = 0 then (1 : ℝ) else -1) • A.column i (T p))
      2 (volume.restrict S) := by
    simpa +instances only [Pi.smul_apply, Function.comp_apply] using!
      ((Lp.memLp (A.column i)).comp_measurePreserving
        m64AnnulusRadialFlip_restrict_measurePreserving).const_smul
          (if i = 0 then (1 : ℝ) else -1)
  have hbelow : (∫ p in S, psi p • ((if i = 0 then (1 : ℝ) else -1) • A.column i (T p))) +
      (∫ p in S, dphi (p - v) • e (A.map (T p))) =
      if i = 1 then ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 0) • e (c0 x) else 0 := by
    have hflip := m64AnnulusRadialFlip_green (e ∘ A.map) (A.column i) hpsi i
    have heta : ContDiff ℝ 1 (psi ∘ T) :=
      hpsi.comp (m64AnnulusRadialFlip_contDiff.of_le (by simp))
    have he := A.observed_lower_green heta
      (fun x => by simp only [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
        m64AnnulusPoint_sub_radialTranslation, sub_self, zero_sub, hbottom])
      (fun s => by simp only [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
        m64AnnulusPoint_sub_radialTranslation, hleft])
      (fun s => by simp only [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
        m64AnnulusPoint_sub_radialTranslation, hright]) i
    simp only [hder] at hflip
    dsimp only [Function.comp_apply] at hflip he
    rw [he] at hflip
    fin_cases i <;> simpa [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
      m64AnnulusPoint_sub_radialTranslation] using hflip
  have hcol := m64AnnulusLowerExtend_integral_smul hW (Lp.memLp (A.column i)) hpM
  have hval := m64AnnulusLowerExtend_integral_smul hF A.observed_memLp hdM
  rw [lowerReflectedColumn, lowerReflectedValue, hcol, hval]
  have habove := A.observed_lower_green hp htop hleft hright i
  dsimp only [Function.comp_apply] at *
  change (∫ p in S, phi p • A.column i p) +
    (∫ p in S, psi p • ((if i = 0 then (1 : ℝ) else -1) • A.column i (T p))) +
    ((∫ p in S, dphi p • e (A.map p)) + ∫ p in S, dphi (p - v) • e (A.map (T p))) = 0
  calc
    _ = ((∫ p in S, phi p • A.column i p) + ∫ p in S, dphi p • e (A.map p)) +
        ((∫ p in S, psi p • ((if i = 0 then (1 : ℝ) else -1) • A.column i (T p))) +
          ∫ p in S, dphi (p - v) • e (A.map (T p))) := by abel
    _ = 0 := by rw [habove, hbelow]; split_ifs <;> abel



theorem lower_reflected_weak (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (i : Fin 2) (b : Fin m) :
    HasWeakPartialDeriv i (fun p => A.lowerReflectedColumn i p b)
      (fun p => A.lowerReflectedValue p b) O := by
  intro phi hp hc hs
  have hpM : MemLp phi 2 (volume.restrict O) :=
    (hp.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdM : MemLp (fun p => fderiv ℝ phi p (ei i)) 2 (volume.restrict O) :=
    (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  let L := EuclideanSpace.proj (𝕜 := ℝ) b
  have hproj (f : LoopPlane → E) (hf : MemLp f 2 (volume.restrict O))
      (psi : LoopPlane → ℝ) (hpsi : MemLp psi 2 (volume.restrict O)) :
      L (∫ p in O, psi p • f p) = ∫ p in O, psi p * f p b := by
    simpa only [map_smul, smul_eq_mul, L, EuclideanSpace.coe_proj] using
      (L.integral_comp_comm (m64L2_test_integrable hf hpsi)).symm
  have h := congrArg L (A.lower_reflected_green (hp.of_le (by simp)) hc hs i)
  simp only [map_add, map_zero] at h
  rw [hproj _ (A.lower_reflected_memLp.2 i) _ hpM,
    hproj _ A.lower_reflected_memLp.1 _ hdM] at h
  simp only [mul_comm] at h ⊢
  linarith

end PoincareConjecture.M64ObservedWeakAnnulus
