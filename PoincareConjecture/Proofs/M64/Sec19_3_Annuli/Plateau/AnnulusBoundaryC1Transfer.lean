import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialCompletion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceAffineBoundaryInverse

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem m64AnnulusRadialCompletion_lower_contMDiffWithinAt
    (f : LoopPlane → M) (c0 c1 : ℝ → M) (x : ℝ) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (U : LoopPlane → M)
    (hU : ContMDiffOn (𝓡 2) (𝓡 n) 1 U
      (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}))
    (heq : EqOn U (f ∘ m64SourceAffine (annulusPoint x 0) s hs.ne')
      (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}))
    (htrace : ∀ z ∈ closedBall (0 : LoopPlane) r, z 1 = 0 → U z = c0 (x + s * z 0)) :
    ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 (m64AnnulusRadialCompletion f c0 c1)
      {p : LoopPlane | 0 ≤ p 1} (annulusPoint x 0) := by
  let Phi := m64SourceAffine (annulusPoint x 0) s hs.ne'
  let F := m64AnnulusRadialCompletion f c0 c1
  let H : Set LoopPlane := {p | 0 ≤ p 1}
  have hzero : (0 : LoopPlane) ∈ H := by simp [H]
  have hU0 : ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 U H 0 :=
    (hU 0 ⟨mem_closedBall_self hr.le, hzero⟩).mono_of_mem_nhdsWithin
      (inter_mem (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds 0 hr)) self_mem_nhdsWithin)
  have hlt : {z : LoopPlane | (Phi z) 1 < 1} ∈ 𝓝 0 := by
    apply (isOpen_lt (by fun_prop) continuous_const).mem_nhds
    change (m64SourceAffine (annulusPoint x 0) s hs.ne' 0) 1 < 1
    rw [m64SourceAffine_zero]
    norm_num [annulusPoint]
  have hagree : F ∘ Phi =ᶠ[𝓝[H] 0] U := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : LoopPlane) hr),
      mem_nhdsWithin_of_mem_nhds hlt, self_mem_nhdsWithin] with z hz hzlt hzH
    change F (Phi z) = U z
    by_cases hz0 : z 1 = 0
    · change m64AnnulusRadialCompletion f c0 c1 (Phi z) = U z
      rw [show Phi z = annulusPoint (x + s * z 0) 0 from
        m64AnnulusSourceAffine_face x s hs.ne' hz0, m64AnnulusRadialCompletion_lower]
      exact (htrace z (ball_subset_closedBall hz) hz0).symm
    · have hzpos : 0 < z 1 := lt_of_le_of_ne hzH (Ne.symm hz0)
      have hp : (Phi z) 1 ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨?_, hzlt⟩
        rw [(m64AnnulusSourceAffine_coordinates x s hs.ne' z).2]
        exact mul_pos (inv_pos.mpr hs) hzpos
      exact (m64AnnulusRadialCompletion_interior f c0 c1 hp).trans (heq ⟨hz, hzpos⟩).symm
  have hF : ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 (F ∘ Phi) H 0 :=
    hU0.congr_of_eventuallyEq_of_mem hagree hzero
  have hInv : ContMDiff (𝓡 2) (𝓡 2) 1 Phi.symm :=
    (m64SourceAffine_symm_contDiff (annulusPoint x 0) s hs.ne').contMDiff
  have hh := hF.comp_of_eq (hInv (annulusPoint x 0)).contMDiffWithinAt
    (m64AnnulusSourceAffine_symm_halfPlane x hs)
    (m64SourceAffine_symm_center (annulusPoint x 0) s hs.ne')
  simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hh

theorem m64AnnulusRadialCompletion_upper_contMDiffWithinAt
    (f : LoopPlane → M) (c0 c1 : ℝ → M) (x : ℝ) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (U : LoopPlane → M)
    (hU : ContMDiffOn (𝓡 2) (𝓡 n) 1 U
      (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}))
    (heq : EqOn U (f ∘ (m64AnnulusRadialFlip ∘
      m64SourceAffine (annulusPoint x 0) s hs.ne'))
      (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}))
    (htrace : ∀ z ∈ closedBall (0 : LoopPlane) r, z 1 = 0 → U z = c1 (x + s * z 0)) :
    ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 (m64AnnulusRadialCompletion f c0 c1)
      {p : LoopPlane | p 1 ≤ 1} (annulusPoint x 1) := by
  have hlow := m64AnnulusRadialCompletion_lower_contMDiffWithinAt
    (f ∘ m64AnnulusRadialFlip) c1 c0 x hs hr U hU heq htrace
  rw [m64AnnulusRadialCompletion_flip] at hlow
  have hT : ContMDiff (𝓡 2) (𝓡 2) 1 m64AnnulusRadialFlip :=
    (m64AnnulusRadialFlip_contDiff.of_le (by simp)).contMDiff
  have hmap : MapsTo m64AnnulusRadialFlip {p : LoopPlane | p 1 ≤ 1}
      {p : LoopPlane | 0 ≤ p 1} := by
    intro p hp
    change 0 ≤ m64AnnulusRadialFlip p 1
    have hc : m64AnnulusRadialFlip p 1 = 1 - p 1 := by
      simp [m64AnnulusRadialFlip_apply, m60PlaneReflection_apply, annulusPoint, sub_eq_add_neg]
    rw [hc]
    exact sub_nonneg.mpr hp
  have hcenter : m64AnnulusRadialFlip (annulusPoint x 1) = annulusPoint x 0 := by
    rw [m64AnnulusRadialFlip_point, sub_self]
  have hh := hlow.comp_of_eq (hT (annulusPoint x 1)).contMDiffWithinAt hmap hcenter
  have hTT (p : LoopPlane) : m64AnnulusRadialFlip (m64AnnulusRadialFlip p) = p :=
    m64AnnulusRadialFlip_involutive p
  simpa only [Function.comp_def, hTT] using hh

end PoincareConjecture
