import PoincareConjecture.Proofs.M47.TerminalCurvatureNeckChartError
import PoincareConjecture.Proofs.M13.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace E M] [ChartedSpace E X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]

theorem terminalCurvature_pullback_coefficient_germ
    (h : RiemannianMetric 3 X) {f f0 : E → X} {x : E}
    (heq : f =ᶠ[𝓝 x] f0) :
    h.pullbackCoefficients f =ᶠ[𝓝 x] h.pullbackCoefficients f0 := by
  filter_upwards [heq.eventually_nhds] with y hy
  have hgerm : f =ᶠ[𝓝 y] f0 := hy
  have hd := hgerm.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  ext a b
  change h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y a)
      (mfderiv (𝓡 3) (𝓡 3) f y b) =
    h.inner (f0 y) (mfderiv (𝓡 3) (𝓡 3) f0 y a)
      (mfderiv (𝓡 3) (𝓡 3) f0 y b)
  rw [hd]
  exact congrArg (fun z : X => h.inner z
    (mfderiv (𝓡 3) (𝓡 3) f0 y a)
    (mfderiv (𝓡 3) (𝓡 3) f0 y b)) hgerm.eq_of_nhds

omit [IsManifold (𝓡 3) ∞ M] in

theorem terminalCurvature_inverse_chart_coefficient_germ
    (h : RiemannianMetric 3 X)
    (psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    {y : E} (hy : y ∈ (psi.trans c).target) :
    h.pullbackCoefficients (psi ∘ (psi.trans c).symm) =ᶠ[𝓝 y]
      h.pullbackCoefficients c.symm := by
  apply terminalCurvature_pullback_coefficient_germ
  filter_upwards [(psi.trans c).open_target.mem_nhds hy] with z hz
  change z ∈ c.target ∧ c.symm z ∈ psi.target at hz
  exact psi.right_inv hz.2

theorem terminalCurvature_inverse_chart_error_jet
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 X)
    (psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    {y : E} (hy : y ∈ (psi.trans c).target) (lambda : ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (fun z => lambda •
      (h.pullbackCoefficients (psi ∘ (psi.trans c).symm) z -
        g.pullbackCoefficients (psi.trans c).symm z)) y =
      lambda • (iteratedFDeriv ℝ j (h.pullbackCoefficients c.symm) y -
        iteratedFDeriv ℝ j (g.pullbackCoefficients (psi.trans c).symm) y) := by
  have htarget : y ∈ c.target := hy.1
  have hs := g.contDiffAt_pullbackCoefficients
    ((psi.trans c).contMDiffOn_invFun.contMDiffAt
      ((psi.trans c).open_target.mem_nhds hy))
  have ht := h.contDiffAt_pullbackCoefficients
    (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget))
  have heq := terminalCurvature_inverse_chart_coefficient_germ h psi c hy
  have herr : (fun z => lambda •
      (h.pullbackCoefficients (psi ∘ (psi.trans c).symm) z -
        g.pullbackCoefficients (psi.trans c).symm z)) =ᶠ[𝓝 y]
      fun z => lambda • (h.pullbackCoefficients c.symm z -
        g.pullbackCoefficients (psi.trans c).symm z) := by
    filter_upwards [heq] with z hz
    rw [hz]
  have hjetEq := herr.iteratedFDeriv (𝕜 := ℝ) j
  rw [hjetEq.eq_of_nhds]
  have hsub : ContDiffAt ℝ j
      (fun z => h.pullbackCoefficients c.symm z -
        g.pullbackCoefficients (psi.trans c).symm z) y :=
    (ht.sub hs).of_le (by exact_mod_cast le_top)
  calc
    iteratedFDeriv ℝ j (fun z => lambda •
        (h.pullbackCoefficients c.symm z -
          g.pullbackCoefficients (psi.trans c).symm z)) y =
        lambda • iteratedFDeriv ℝ j
          (fun z => h.pullbackCoefficients c.symm z -
            g.pullbackCoefficients (psi.trans c).symm z) y :=
      iteratedFDeriv_const_smul_apply' hsub
    _ = lambda • (iteratedFDeriv ℝ j (h.pullbackCoefficients c.symm) y -
        iteratedFDeriv ℝ j (g.pullbackCoefficients (psi.trans c).symm) y) := by
      congr 1
      exact iteratedFDeriv_sub_apply (i := j)
        (f := h.pullbackCoefficients c.symm)
        (g := g.pullbackCoefficients (psi.trans c).symm)
        (ht.of_le (by exact_mod_cast le_top)) (hs.of_le (by exact_mod_cast le_top))

theorem terminalCurvature_scaled_pullback_coefficients
    (g : RiemannianMetric 3 M) {lambda : ℝ} (hlambda : 0 < lambda) (f : E → M) :
    RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric g lambda hlambda) f =
      fun y => lambda • g.pullbackCoefficients f y := by
  funext y
  ext a b
  rfl

end PoincareConjecture.M47
