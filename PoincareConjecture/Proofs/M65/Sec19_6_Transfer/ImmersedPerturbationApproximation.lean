import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationParameters
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationTopology












set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {a b : ℝ} {J : Set ℝ} {s t : ℝ}






theorem m65Exists_generic_residual_approximation (F : RicciFlow 3 M (Icc a b))
    (hJ : IsOpen J) (hJF : J ⊆ Ioo a b) (C : M65SmoothFilledLoopFamily F J)
    (hCSF : ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (fun u => periodicFreeLoop (C.loops u) x) q =
        m62CurvatureVector F (fun y u => periodicFreeLoop (C.loops u) y) q x)
    (hst : s ≤ t) (hI : Icc s t ⊆ J) :
    ∃ (ell r : ℝ) (loops : ℕ → ℝ → C1FreeLoopSpace (M := M))
        (exceptions : ℕ → Finset ℝ) (L : ℝ),
      ell < s ∧ t < r ∧ Icc ell r ⊆ J ∧ 0 ≤ L ∧
      (∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞
        (fun z => periodicFreeLoop (loops n z.2) z.1) (univ ×ˢ Ioo ell r)) ∧
      (∀ n q, q ∈ Ioo ell r → ∀ x,
        curveVelocity (n := 3) (periodicFreeLoop (loops n q)) x ≠ 0) ∧
      (∀ n q, q ∈ Icc s t → q ∉ exceptions n →
        Function.Injective (loops n q : LoopCircle → M)) ∧
      (∀ n q, q ∈ Icc s t → ∀ x,
        (F.metric q).tangentNorm (periodicFreeLoop (loops n q) x)
          (curveVelocity (n := 3) (fun u => periodicFreeLoop (loops n u) x) q -
            m62CurvatureVector F (fun y u => periodicFreeLoop (loops n u) y) q x) ≤
              1 / ((n : ℝ) + 1)) ∧
      (∀ n q, q ∈ Icc s t → freeLoopLength (F.metric q) (loops n q) ≤ L) ∧
      (∀ q, q ∈ Ioo ell r → Tendsto (fun n => loops n q) atTop (𝓝 (C.loops q))) ∧
      ∀ n, ContinuousOn (loops n) (Ioo ell r) := by
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
  have hfin (n : ℕ) :
      {q | q ∈ Icc s t ∧ ¬Function.Injective (Gamma (p n) q : LoopCircle → M)}.Finite :=
    hfinite (p n) (hproperties n).1 (hproperties n).2.1
  let loops := fun n q => Gamma (p n) q
  let exceptions := fun n => (hfin n).toFinset
  refine ⟨ell, r, loops, exceptions, L, hell, htr, hKJ, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hGamma.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      (fun z hz => ⟨(hproperties n).1, hz⟩)
  · intro n q hq x
    exact himm (p n) (hproperties n).1 q hq x
  · intro n q hq hnot
    by_contra hnon
    apply hnot
    exact (hfin n).mem_toFinset.mpr ⟨hq, hnon⟩
  · intro n q hq
    exact (hproperties n).2.2.1 q hq
  · intro n q hq
    exact (hproperties n).2.2.2 q hq
  · intro q hq
    exact M65Perturbation.loop_tendsto_of_parameter Gamma isOpen_ball isOpen_Ioo hGamma
      p 0 (mem_ball_self hdelta) hp q hq (C.loops q) (hbase q hq)
  · intro n
    exact (M65Perturbation.loop_family_continuousOn Gamma isOpen_ball isOpen_Ioo hGamma).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun q hq => ⟨(hproperties n).1, hq⟩)

end PoincareConjecture
