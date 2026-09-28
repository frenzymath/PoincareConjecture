import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseHalfDiskGraph
import PoincareConjecture.Proofs.M64.Mathlib.HalfDiskC1Green

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ
local notation "nu" => volume.restrict (Icc (0 : ℝ) Real.pi)

theorem lower_halfDisk_real_phase
    (A : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (he : Continuous e)
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {x H epsilon R : ℝ} (hx : H < x) (hP : x + H < curvePeriod) (hH : H < 1)
    (hepsilon : 0 < epsilon) (hRH : R ≤ H) :
    let u := fun z => A.phase (z + annulusPoint x 0)
    let V := fun i z => A.phaseColumn i (z + annulusPoint x 0)
    let b := fun s => H0 (A.label0 (s + x))
    ∀ᵐ r ∂volume.restrict (Icc epsilon R),
      let d := fun theta => -r * Real.sin theta * V 0 (r • angularPoint theta) +
        r * Real.cos theta * V 1 (r • angularPoint theta)
      MemLp d 2 nu ∧ ∃ L : ℝ → ℝ,
        AbsolutelyContinuousOnInterval L 0 Real.pi ∧
        (L =ᵐ[nu] fun theta => u (r • angularPoint theta)) ∧
        L 0 = b r ∧ L Real.pi = b (-r) ∧
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          L t - L s = ∫ theta in s..t, d theta) ∧
        (∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ i : Fin 2,
          (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
            V i z * test z + u z * fderiv ℝ test z (basis i)) =
            r * (∫ theta in (0 : ℝ)..Real.pi,
              L theta * test (r • angularPoint theta) * angularPoint theta i) -
            (basis 1) i * ∫ s in (-r)..r, b s * test (s • basis 0)) ∧
        ∀ gamma : ℝ → M, ContinuousOn gamma (Icc (0 : ℝ) Real.pi) →
          (gamma =ᵐ[nu] fun theta => A.annulus.map
            (r • angularPoint theta + annulusPoint x 0)) →
          ∀ theta ∈ Icc (0 : ℝ) Real.pi,
            Robs (e (gamma theta)) = angularPoint (k * L theta) := by
  obtain ⟨hu, hV, hb, f, hf, hval, hcol, htrace⟩ :=
    A.lower_halfDisk_phase_graph_approximation hH0 hH1 hx hP hH
  have hline (s : ℝ) : s • basis 0 = annulusPoint s 0 := by
    ext i
    fin_cases i <;> simp [annulusPoint, EuclideanSpace.basisFun_apply]
  have hdata := m64HalfDisk_strong_graph_extract hepsilon hRH
    (fun z => A.phase (z + annulusPoint x 0))
    (fun i z => A.phaseColumn i (z + annulusPoint x 0))
    (fun s => H0 (A.label0 (s + x))) hu hV hb f hf hval
    (fun i => by simpa only [EuclideanSpace.basisFun_apply] using hcol i)
    (by simpa only [hline] using htrace)
  let T := fun z : LoopPlane => z + annulusPoint x 0
  have hT : MeasurePreserving T volume volume := measurePreserving_add_right volume _
  have hobs := m64HalfDisk_polar_ae hepsilon hRH
    (m64MeasurePreserving_ae_restrict hT isOpen_interior.measurableSet
      (m64Annulus_halfDisk_ae_mem hx hP hH) A.phase_observation)
  filter_upwards [hdata, hobs, ae_restrict_mem measurableSet_Icc] with r hr hobsr hrI
  obtain ⟨hm, hgreen, hd, L, hL, hLA, hL0, hLpi, hinc⟩ := hr
  refine ⟨hd, L, hL, hLA, hL0, hLpi, hinc, ?_, ?_⟩
  · intro test htest i
    have hrpos : 0 < r := hepsilon.trans_le hrI.1
    have hrH : r ≤ H := hrI.2.trans hRH
    have hKr : closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} ⊆
        closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1} :=
      inter_subset_inter (closedBall_subset_closedBall hrH) Subset.rfl
    let : IsFiniteMeasure (volume.restrict
        (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})) := isFiniteMeasure_restrict.mpr
      ((isCompact_closedBall (0 : LoopPlane) r).inter_right
        (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)).measure_lt_top.ne
    have huL := (hu.mono_measure (Measure.restrict_mono hKr le_rfl)).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
    have hVL (j : Fin 2) := ((hV j).mono_measure
      (Measure.restrict_mono hKr le_rfl)).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hbL := (hb.mono_measure (Measure.restrict_mono
      (Icc_subset_Icc (neg_le_neg hrH) hrH) le_rfl)).integrable
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hLL : Integrable L nu := (hm.integrable (by norm_num)).congr hLA.symm
    apply m64HalfDisk_green_contDiff hrpos _ _ _ L huL hVL hbL hLL _ test htest i
    intro phi j
    rw [hgreen phi j]
    congr 2
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : uIoc (0 : ℝ) Real.pi ⊆ Icc (0 : ℝ) Real.pi := by
      rw [uIoc_of_le Real.pi_pos.le]
      exact Ioc_subset_Icc_self
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hLA] with theta htheta
    rw [htheta]
  · intro gamma hgamma hgammaAE
    have hAE : (fun theta => Robs (e (gamma theta))) =ᵐ[nu]
        fun theta => angularPoint (k * L theta) := by
      filter_upwards [hgammaAE, hLA, hobsr] with theta hg hl ho
      rw [hg, hl]
      exact ho
    have hLc : ContinuousOn L (Icc (0 : ℝ) Real.pi) := by
      simpa only [uIcc_of_le Real.pi_pos.le] using hL.continuousOn
    have hc : ContinuousOn (fun theta => angularPoint (k * L theta))
        (Icc (0 : ℝ) Real.pi) :=
      contDiff_angularPoint.continuous.comp_continuousOn
        (continuous_const.continuousOn.mul hLc)
    exact fun theta htheta => Measure.eqOn_Icc_of_ae_eq volume Real.pi_pos.ne hAE
      (Robs.continuous.comp_continuousOn (he.comp_continuousOn hgamma)) hc htheta

end PoincareConjecture.M64FreeWeakPhaseAnnulus
