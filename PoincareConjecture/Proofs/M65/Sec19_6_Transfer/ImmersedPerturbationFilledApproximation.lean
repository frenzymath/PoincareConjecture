import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationApproximation
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationFilling
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationAreaContinuity

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {a b circumference : ℝ} {J : Set ℝ} {s t : ℝ}

theorem m65Exists_generic_filled_approximations (F : RicciFlow 3 M (Icc a b))
    (P : M62.CircleProductData F circumference)
    (hJ : IsOpen J) (hJF : J ⊆ Ioo a b)
    (disks : ∀ q ∈ J, M64DiskAreaComparison P q) (C : M65SmoothFilledLoopFamily F J)
    (hCSF : ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (fun u => periodicFreeLoop (C.loops u) x) q =
        m62CurvatureVector F (fun y u => periodicFreeLoop (C.loops u) y) q x)
    (hst : s ≤ t) (hI : Icc s t ⊆ J) :
    ∃ (ell r : ℝ) (Cn : ℕ → M65SmoothFilledLoopFamily F (Ioo ell r))
        (exceptions : ℕ → Finset ℝ) (L : ℝ),
      ell < s ∧ t < r ∧ Icc ell r ⊆ J ∧ 0 ≤ L ∧
      (∀ n q, q ∈ Icc s t → q ∉ exceptions n →
        Function.Injective ((Cn n).loops q : LoopCircle → M)) ∧
      (∀ n q, q ∈ Icc s t → ∀ x,
        (F.metric q).tangentNorm (periodicFreeLoop ((Cn n).loops q) x)
          (curveVelocity (n := 3) (fun u => periodicFreeLoop ((Cn n).loops u) x) q -
            m62CurvatureVector F (fun y u => periodicFreeLoop ((Cn n).loops u) y) q x) ≤
              1 / ((n : ℝ) + 1)) ∧
      (∀ n q, q ∈ Icc s t → freeLoopLength (F.metric q) ((Cn n).loops q) ≤ L) ∧
      (∀ q, q ∈ Ioo ell r →
        Tendsto (fun n => (Cn n).loops q) atTop (𝓝 (C.loops q))) ∧
      (∀ n, ContinuousOn (Cn n).loops (Ioo ell r)) ∧
      (∀ n, ContinuousOn
        (fun q => fillingArea (F.metric q) ((Cn n).loops q)) (Ioo ell r)) ∧
      ∀ q, q ∈ Ioo ell r → Tendsto
        (fun n => fillingArea (F.metric q) ((Cn n).loops q)) atTop
        (𝓝 (fillingArea (F.metric q) (C.loops q))) := by
  classical
  obtain ⟨ell, r, N, delta, Gamma, Bad, hell, htr, hKJ, hdelta,
    hGamma, hbase, himm, hBad, hfinite⟩ :=
      m65Exists_generic_loop_perturbation F hJ hJF C hst hI
  have hOJ : Ioo ell r ⊆ J := Ioo_subset_Icc_self.trans hKJ
  have hIO : Icc s t ⊆ Ioo ell r := fun q hq =>
    ⟨hell.trans_le hq.1, hq.2.trans_lt htr⟩
  let D : M65SmoothFilledLoopFamily F (Ioo ell r) := {
    loops := C.loops
    joint_smooth := C.joint_smooth.mono (prod_mono Subset.rfl hOJ)
    immersed := fun q hq => C.immersed q (hOJ hq)
    filled := fun q hq => C.filled q (hOJ hq) }
  obtain ⟨p, L, hp, hL, hproperties⟩ := M65Perturbation.exists_controlled_generic_parameters
    F isOpen_Ioo (hOJ.trans hJF) D Gamma delta hdelta Bad hBad hGamma himm hbase
      (fun q hq => hCSF q (hOJ hq)) (Icc s t) isCompact_Icc hIO
  let Cn : ℕ → M65SmoothFilledLoopFamily F (Ioo ell r) := fun n => {
    loops := Gamma (p n)
    joint_smooth := hGamma.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      (fun z hz => ⟨(hproperties n).1, hz⟩)
    immersed := fun q hq => himm (p n) (hproperties n).1 q hq
    filled := by
      intro q hq
      obtain ⟨D0⟩ := C.filled q (hOJ hq)
      obtain ⟨Dp, _⟩ := M65Perturbation.parameter_filling P q (disks q (hOJ hq))
        Gamma hGamma (hproperties n).1 hq (C.loops q) (hbase q hq) D0 1 zero_lt_one
      exact ⟨Dp⟩ }
  have hfin (n : ℕ) :
      {q | q ∈ Icc s t ∧ ¬Function.Injective ((Cn n).loops q : LoopCircle → M)}.Finite :=
    hfinite (p n) (hproperties n).1 (hproperties n).2.1
  let exceptions := fun n => (hfin n).toFinset
  have hconv (q : ℝ) (hq : q ∈ Ioo ell r) :
      Tendsto (fun n => (Cn n).loops q) atTop (𝓝 (C.loops q)) :=
    M65Perturbation.loop_tendsto_of_parameter Gamma isOpen_ball isOpen_Ioo hGamma
      p 0 (mem_ball_self hdelta) hp q hq (C.loops q) (hbase q hq)
  have hcontinuous (n : ℕ) : ContinuousOn (Cn n).loops (Ioo ell r) :=
    (M65Perturbation.loop_family_continuousOn Gamma isOpen_ball isOpen_Ioo hGamma).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun q hq => ⟨(hproperties n).1, hq⟩)
  refine ⟨ell, r, Cn, exceptions, L, hell, htr, hKJ, hL, ?_, ?_, ?_, hconv,
    hcontinuous, ?_, ?_⟩
  · intro n q hq hnot
    by_contra hnon
    exact hnot ((hfin n).mem_toFinset.mpr ⟨hq, hnon⟩)
  · intro n q hq
    exact (hproperties n).2.2.1 q hq
  · intro n q hq
    exact (hproperties n).2.2.2 q hq
  · intro n
    exact M65Perturbation.fillingArea_continuousOn P
      (hOJ.trans (hJF.trans Ioo_subset_Icc_self)) (fun q hq => disks q (hOJ hq))
      (Cn n).loops (hcontinuous n) (Cn n).filled
  · intro q hq
    exact (m65FillingArea_tendsto_of_C1 P q (disks q (hOJ hq)) isCompact_univ
      (fun n => (Cn n).loops q) (C.loops q) (hconv q hq)
      (fun n => (Cn n).filled q hq)).2

end PoincareConjecture
