import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses
import PoincareConjecture.Definitions.M63Ramp
import Mathlib.Analysis.Calculus.Deriv.MeanValue










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}





theorem normal_relabeling_derivative_eq_zero
    {c : ℝ → ℝ → M} {psi : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J)
    (hcomp : M63C2ShrinkingCurveOn F (fun x t => c (psi x t) t) J)
    {t x w : ℝ} (ht : t ∈ interior J)
    (hpsi : Differentiable ℝ (fun y => psi y t))
    (hpos : ∀ y, 0 < deriv (fun z => psi z t) y)
    (htime : HasDerivAt (psi x) w t) : w = 0 := by
  have htJ : t ∈ J := interior_subset ht
  have hq : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 n)
      (fun z : ℝ × ℝ => c z.1 z.2) (psi x t, t) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact ((hc.joint_c1 (psi x t, t) ⟨mem_univ _, ht⟩).contMDiffAt
      ((isOpen_univ.prod isOpen_interior).mem_nhds ⟨mem_univ _, ht⟩)).mdifferentiableAt
        (by simp)
  have hS := unitTangent_contMDiff_of_c2 F c (hc.spatial_regular t htJ) (hc.immersed t htJ)
  have hcurvature : m62CurvatureVector F (fun y s => c (psi y s) s) t x =
      m62CurvatureVector F c t (psi x t) :=
    curvatureVector_comp F c
      ((hc.spatial_regular t htJ).mdifferentiable (by norm_num)) hpsi hpos
      ((hS (psi x t)).mdifferentiableAt (by simp))
  have hchain := curveVelocity_moving_labels c hq htime
  rw [hcomp.equation t ht x, hc.equation t ht (psi x t), hcurvature] at hchain
  have hzero : w • curveVelocity (n := n) (fun y => c y t) (psi x t) = 0 :=
    add_eq_right.mp hchain.symm
  exact (smul_eq_zero.mp hzero).resolve_right (hc.immersed t htJ (psi x t))





theorem normal_relabeling_eq_initial_labels
    {c : ℝ → ℝ → M} {psi : ℝ → ℝ → ℝ} {s T : ℝ}
    (hc : M63C2ShrinkingCurveOn F c (Icc s T))
    (hcomp : M63C2ShrinkingCurveOn F (fun x t => c (psi x t) t) (Icc s T))
    (hcont : ∀ x, ContinuousOn (psi x) (Icc s T))
    (htime : ∀ x t, t ∈ Ioo s T → DifferentiableAt ℝ (psi x) t)
    (hspace : ∀ t ∈ Ioo s T, Differentiable ℝ (fun x => psi x t))
    (hpos : ∀ t ∈ Ioo s T, ∀ x, 0 < deriv (fun y => psi y t) x)
    (hinit : ∀ x, psi x s = x) :
    ∀ t ∈ Icc s T, ∀ x, psi x t = x := by
  intro t ht x
  have hderiv (r : ℝ) (hr : r ∈ interior (Icc s T)) :
      HasDerivWithinAt (psi x) 0 (interior (Icc s T)) r := by
    have hr' : r ∈ Ioo s T := by simpa only [interior_Icc] using hr
    have hd := (htime x r hr').hasDerivAt
    have hzero := normal_relabeling_derivative_eq_zero hc hcomp hr
      (hspace r hr') (hpos r hr') hd
    rw [hzero] at hd
    exact hd.hasDerivWithinAt
  have hm : MonotoneOn (psi x) (Icc s T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s T) (hcont x) hderiv
      (fun _ _ => le_rfl)
  have ha : AntitoneOn (psi x) (Icc s T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s T) (hcont x) hderiv
      (fun _ _ => le_rfl)
  have hs : s ∈ Icc s T := ⟨le_rfl, ht.1.trans ht.2⟩
  exact (le_antisymm (ha hs ht ht.1) (hm hs ht ht.1)).trans (hinit x)

end PoincareConjecture.M63
