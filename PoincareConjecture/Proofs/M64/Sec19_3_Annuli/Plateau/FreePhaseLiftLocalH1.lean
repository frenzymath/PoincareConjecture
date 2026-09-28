import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCoordinateCorrection
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularAngles
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

theorem m64ContinuousPhase_local_angle
    {u : LoopPlane → ℝ} {q : LoopPlane → LoopPlane} {k : ℝ} (hk : k ≠ 0)
    (hu : Continuous u) (hq : Continuous q)
    (hphase : ∀ p, q p = angularPoint (k * u p)) (a : LoopPlane) :
    ∃ (V : Set LoopPlane) (F : LoopPlane → ℝ),
      IsOpen V ∧ q a ∈ V ∧ ContDiffOn ℝ 1 F V ∧ u =ᶠ[𝓝 a] F ∘ q := by
  have hnorm (p : LoopPlane) : ‖q p‖ = 1 := by rw [hphase, norm_angularPoint]
  have hzero : q a ≠ 0 := by
    intro h
    have hh := hnorm a
    rw [h, norm_zero] at hh
    norm_num at hh
  obtain ⟨theta, htheta, hpolar⟩ := m60_exists_contDiffAt_planeAngle hzero
  have hangle (p : LoopPlane) : angularPoint (theta (q p)) = angularPoint (k * u p) := by
    have h := hpolar (q p)
    rw [hnorm, one_smul] at h
    exact h.trans (hphase p)
  have hexp (p : LoopPlane) : Circle.exp (theta (q p)) = Circle.exp (k * u p) := by
    rw [← m60LoopCircleHomeomorphCircle_angular, ← m60LoopCircleHomeomorphCircle_angular]
    congr 1
    exact Subtype.ext (hangle p)
  let F := fun z => (theta z - theta (q a)) / k + u a
  have hFa : F (q a) = u a := by simp only [F, sub_self, zero_div, zero_add]
  have hF : ContDiffAt ℝ 1 F (q a) :=
    ((htheta.sub contDiffAt_const).div_const k).add contDiffAt_const
  obtain ⟨V0, hV0, hF0⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVV, hV, haV⟩ := _root_.mem_nhds_iff.mp hV0
  have hFk (z : LoopPlane) : k * F z = theta z - theta (q a) + k * u a := by
    dsimp only [F]
    field_simp
  have hFeq (p : LoopPlane) : Circle.exp (k * F (q p)) = Circle.exp (k * u p) := by
    rw [hFk, Circle.exp_add, Circle.exp_sub, hexp p, hexp a]
    exact div_mul_cancel _ _
  obtain ⟨I, hI, haI, hinj⟩ :=
    Circle.isCoveringMap_exp.isLocalHomeomorph.isLocallyInjective (k * u a)
  have hleft : ∀ᶠ p in 𝓝 a, k * u p ∈ I :=
    (continuous_const.mul hu).continuousAt.preimage_mem_nhds (hI.mem_nhds haI)
  have hright : ∀ᶠ p in 𝓝 a, k * F (q p) ∈ I := by
    have hcont : ContinuousAt (fun p => k * F (q p)) a :=
      continuousAt_const.mul (hF.continuousAt.comp hq.continuousAt)
    apply hcont.preimage_mem_nhds
    rw [hFa]
    exact hI.mem_nhds haI
  refine ⟨V, F, hV, haV, hF0.mono hVV, ?_⟩
  filter_upwards [hleft, hright] with p hp hFp
  exact (mul_left_cancel₀ hk) (hinj hp hFp (hFeq p).symm)

theorem m64ContinuousPhase_local_memW1p
    {O : Set LoopPlane} (hO : IsOpen O)
    {u : LoopPlane → ℝ} {q : LoopPlane → LoopPlane}
    {Z : Fin 2 → LoopPlane → LoopPlane} {k : ℝ} (hk : k ≠ 0)
    (hu : Continuous u) (hq : Continuous q)
    (hZ : ∀ i, MemLp (Z i) 2 (volume.restrict O))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => Z i p j) (fun p => q p j) O)
    (hphase : ∀ p, q p = angularPoint (k * u p)) {a : LoopPlane} (ha : a ∈ O) :
    ∃ r : ℝ, 0 < r ∧ closedBall a r ⊆ O ∧ MemW1p 2 u (ball a r) := by
  obtain ⟨V, F, hV, haV, hF, heq⟩ := m64ContinuousPhase_local_angle hk hu hq hphase a
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem (hO.mem_nhds ha)
      (hq.continuousAt.preimage_mem_nhds (hV.mem_nhds haV))) heq)
  have hsmall : closedBall a (R / 2) ⊆ ball a R := closedBall_subset_ball (half_lt_self hR)
  have hSO : closedBall a (R / 2) ⊆ O := fun p hp => (hball (hsmall hp)).1.1
  have hSV : MapsTo q (closedBall a (R / 2)) V := fun p hp => (hball (hsmall hp)).1.2
  have hseq : EqOn u (F ∘ q) (closedBall a (R / 2)) := fun p hp => (hball (hsmall hp)).2
  let K := q '' closedBall a (R / 2)
  have hK : IsCompact K := (isCompact_closedBall a (R / 2)).image hq
  have hKV : K ⊆ V := by rintro _ ⟨p, hp, rfl⟩; exact hSV hp
  have hsub : ball a (R / 2) ⊆ O := ball_subset_closedBall.trans hSO
  have hhalf : R / 4 < R / 2 := by linarith
  have hlocal := m64WeakCoordinates_scalar_memW1p (show 0 < R / 4 by positivity) hhalf
    hq.continuousOn
    (fun i => (hZ i).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun i j => (hw i j).restrict isOpen_ball hsub) hV hK hKV
    (fun p hp => mem_image_of_mem q hp) hF
  have hinner : ball a (R / 4) ⊆ closedBall a (R / 2) :=
    (ball_subset_ball hhalf.le).trans ball_subset_closedBall
  have hAE : (F ∘ q) =ᵐ[volume.restrict (ball a (R / 4))] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
    exact (hseq (hinner hp)).symm
  refine ⟨R / 4, by positivity,
    (closedBall_subset_closedBall hhalf.le).trans hSO, hlocal.1.ae_eq hAE, ?_⟩
  intro i
  obtain ⟨Wi, hWi, hwWi⟩ := hlocal.2 i
  exact ⟨Wi, hWi, m64WeakPartialDeriv_ae_congr hAE EventuallyEq.rfl hwWi⟩

end PoincareConjecture
