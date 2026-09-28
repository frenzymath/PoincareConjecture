import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseLocalizedGraph
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusLowerDiskCutoff
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusInwardApproximation













noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)





theorem lower_halfDisk_phase_graph_approximation
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {x H : ℝ} (hx : H < x) (hP : x + H < curvePeriod) (hH : H < 1) :
    let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
    let u := fun z => A.phase (z + annulusPoint x 0)
    let V := fun i z => A.phaseColumn i (z + annulusPoint x 0)
    let b := fun s => H0 (A.label0 (s + x))
    MemLp u 2 (volume.restrict K) ∧ (∀ i, MemLp (V i) 2 (volume.restrict K)) ∧
      MemLp b 2 (volume.restrict (Icc (-H) H)) ∧
      ∃ f : ℕ → LoopPlane → ℝ, (∀ j, ContDiff ℝ 1 (f j)) ∧
        Tendsto (fun j => eLpNorm (f j - u) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        (∀ i, Tendsto (fun j => eLpNorm (fun z =>
          fderiv ℝ (f j) z (ei i) - V i z) 2 (volume.restrict K)) atTop (𝓝 0)) ∧
        Tendsto (fun j => eLpNorm (fun s => f j (annulusPoint s 0) - b s)
          2 (volume.restrict (Icc (-H) H))) atTop (𝓝 0) := by
  classical
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  let T := fun z : LoopPlane => z + annulusPoint x 0
  have hT : MeasurePreserving T volume volume := measurePreserving_add_right volume _
  have hbase : ∀ᵐ z ∂volume.restrict K, T z ∈ S := m64Annulus_halfDisk_ae_mem hx hP hH
  have hK : MeasurableSet K := measurableSet_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  obtain ⟨chi, hchi, hc, hs, hnear⟩ := m64Annulus_lower_disk_cutoff hx hP hH
  let F := fun p => chi p * A.lowerReflectedPhase p
  let W := fun i => (O).indicator (fun p => chi p * A.lowerReflectedPhaseColumn i p +
    fderiv ℝ chi p (ei i) * A.lowerReflectedPhase p)
  let beta := fun y => chi (annulusPoint y 0) * H0 (A.label0 y)
  obtain ⟨hF, hW, f, hf, hval, hcol, htrace⟩ :=
    A.localized_lower_phase_graph hH0 hH1 chi hchi hc hs
  have hFae : (F ∘ T) =ᵐ[volume.restrict K] (fun z => A.phase (T z)) := by
    filter_upwards [hbase, ae_restrict_mem hK] with z hz hzK
    have hone : chi (T z) = 1 := (hnear z hzK.1).self_of_nhds
    simp only [Function.comp_apply, F, hone,
      lowerReflectedPhase, m64AnnulusLowerExtend_right _ _ hz, one_mul]
  have hWae (i : Fin 2) : (W i ∘ T) =ᵐ[volume.restrict K]
      (fun z => A.phaseColumn i (T z)) := by
    filter_upwards [hbase, ae_restrict_mem hK] with z hz hzK
    have hone : chi (T z) = 1 := (hnear z hzK.1).self_of_nhds
    have hd : fderiv ℝ chi (T z) = 0 := by
      rw [(hnear z hzK.1).fderiv_eq]
      exact (hasFDerivAt_const (x := T z) (c := (1 : ℝ))).fderiv
    simp only [Function.comp_apply, W, indicator_of_mem (m64AnnulusLower_rect_subset hz),
      hone, hd, zero_apply,
      zero_mul, add_zero, one_mul, lowerReflectedPhaseColumn,
      m64AnnulusLowerExtend_right _ _ hz]
  have hlabel : Continuous (fun s => H0 (A.label0 (s + x))) :=
    (H0.continuous.comp (A.labels_continuous hH0 hH1).1).comp
      (continuous_id.add continuous_const)
  have hb : MemLp (fun s => H0 (A.label0 (s + x))) 2
      (volume.restrict (Icc (-H) H)) :=
    (memLp_two_iff_integrable_sq hlabel.aestronglyMeasurable).mpr
      ((hlabel.pow 2).integrableOn_Icc)
  let g := fun j z => f j (T z)
  have hg (j : ℕ) : ContDiff ℝ 1 (g j) :=
    ((hf j).of_le (by simp)).comp (contDiff_id.add contDiff_const)
  have hder (j : ℕ) (z : LoopPlane) (i : Fin 2) :
      fderiv ℝ (g j) z (ei i) = fderiv ℝ (f j) (T z) (ei i) := by
    dsimp only [g, T]
    rw [fderiv_comp_add_right]
  have hpull {w : LoopPlane → ℝ} (hw : AEStronglyMeasurable w volume) :
      eLpNorm (w ∘ T) 2 (volume.restrict K) ≤ eLpNorm w 2 volume := by
    calc
      _ ≤ eLpNorm (w ∘ T) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = _ := eLpNorm_comp_measurePreserving hw hT
  refine ⟨((hF.comp_measurePreserving hT).restrict K).ae_eq hFae,
    (fun i => (((hW i).comp_measurePreserving hT).restrict K).ae_eq (hWae i)),
    hb, g, hg, ?_, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval
      (fun _ => bot_le)
    intro j
    calc
      _ = eLpNorm ((f j - F) ∘ T) 2 (volume.restrict K) := by
        apply eLpNorm_congr_ae
        filter_upwards [hFae] with z hz
        exact congrArg (fun a => g j z - a) hz.symm
      _ ≤ _ := hpull ((hf j).continuous.aestronglyMeasurable.sub hF.aestronglyMeasurable)
  · intro i
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hcol i)
      (fun _ => bot_le)
    intro j
    calc
      _ = eLpNorm ((fun p => fderiv ℝ (f j) p (ei i) - W i p) ∘ T)
          2 (volume.restrict K) := by
        apply eLpNorm_congr_ae
        filter_upwards [hWae i] with z hz
        dsimp only [Function.comp_apply] at hz
        dsimp only [Function.comp_apply]
        rw [hder, hz]
      _ ≤ _ := hpull ((((hf j).continuous_fderiv (by simp)).clm_apply
          continuous_const).aestronglyMeasurable.sub (hW i).aestronglyMeasurable)
  · have hline : Continuous (fun y : ℝ => annulusPoint y 0) := by
      have hd : ContDiff ℝ 1 (fun y : ℝ => annulusPoint y 0) := by
        apply contDiff_euclidean.mpr
        intro i
        fin_cases i
        · exact contDiff_id
        · exact contDiff_const
      exact hd.continuous
    have hbeta : Continuous beta := (hchi.continuous.comp hline).mul
      (H0.continuous.comp (A.labels_continuous hH0 hH1).1)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htrace
      (fun _ => bot_le)
    intro j
    have hec : Continuous (fun y => f j (annulusPoint y 0) - beta y) :=
      ((hf j).continuous.comp hline).sub hbeta
    have heM : MemLp (fun y => f j (annulusPoint y 0) - beta y)
        2 (volume.restrict I) :=
      (memLp_two_iff_integrable_sq hec.aestronglyMeasurable).mpr
        ((hec.pow 2).integrableOn_Icc)
    have hmem : ∀ᵐ s ∂volume.restrict (Icc (-H) H), s + x ∈ I := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hp := (m64MeasurePreserving_memLp_restrict
      (measurePreserving_add_right volume x) measurableSet_Icc hmem heM).2
    calc
      _ = eLpNorm (fun s => f j (annulusPoint (s + x) 0) - beta (s + x))
          2 (volume.restrict (Icc (-H) H)) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        have hpoint : annulusPoint s 0 ∈ closedBall (0 : LoopPlane) H := by
          have heq : annulusPoint s 0 = EuclideanSpace.single (0 : Fin 2) s := by
            ext i
            fin_cases i <;> simp [annulusPoint]
          rw [mem_closedBall_zero_iff, heq, PiLp.norm_single, Real.norm_eq_abs]
          exact abs_le.mpr hs
        have ht : T (annulusPoint s 0) = annulusPoint (s + x) 0 := by
          ext i
          fin_cases i <;> simp [T, annulusPoint]
        have hone : chi (annulusPoint (s + x) 0) = 1 := by
          rw [← ht]
          exact (hnear _ hpoint).self_of_nhds
        simp only [g, beta, ht, hone, one_mul]
      _ ≤ _ := hp

end PoincareConjecture.M64FreeWeakPhaseAnnulus
