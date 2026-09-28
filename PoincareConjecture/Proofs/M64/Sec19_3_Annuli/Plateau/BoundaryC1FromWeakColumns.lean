import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakClassical













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

local notation "Plane" => EuclideanSpace ℝ (Fin 2)






theorem m64Reflected_contDiffOn_of_continuous_weak_columns
    {m : ℕ} {u : Plane → EuclideanSpace ℝ (Fin m)}
    {P : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict (Metric.ball (0 : Plane) 2)))
    (hP : ∀ i, MemLp (P i) 2 (volume.restrict (Metric.ball (0 : Plane) 2)))
    (hW : ∀ i b, HasWeakPartialDeriv i (fun x => P i x b)
      (fun x => u x b) (Metric.ball (0 : Plane) 2))
    (huc : ContinuousOn u (Metric.ball (0 : Plane) 2))
    (hPc : ∀ i, ContinuousOn (P i) (Metric.ball (0 : Plane) 2)) :
    ContDiffOn ℝ 1 u (Metric.ball (0 : Plane) 1) ∧
      ∀ x ∈ Metric.ball (0 : Plane) 1, ∀ i : Fin 2,
        fderiv ℝ u x (EuclideanSpace.single i 1) = P i x := by
  have hfd (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) 1) :
      HasFDerivAt u (M60.suPlaneColumns (fun i => P i x)) x :=
    M60.suContinuous_weak_gradient_hasFDerivAt hu hP hW huc hPc x hx
  have hderiv : ContinuousOn (fderiv ℝ u) (Metric.ball (0 : Plane) 1) := by
    apply (M60.suPlaneColumns_continuousOn (fun i =>
      (hPc i).mono (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)))).congr
    intro x hx
    exact (hfd x hx).fderiv
  refine ⟨?_, ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    exact ⟨fun x hx => (hfd x hx).differentiableAt.differentiableWithinAt,
      by simp, contDiffOn_zero.mpr hderiv⟩
  · intro x hx i
    rw [(hfd x hx).fderiv]
    fin_cases i <;> simp [M60.suPlaneColumns]

end PoincareConjecture
