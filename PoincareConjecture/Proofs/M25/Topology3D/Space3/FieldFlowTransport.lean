import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowFirstIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set
open scoped ContDiff NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem boundedFlow_chart_pushforward (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (V : E → E) (W : F → F)
    {k l K L : ℝ≥0} (hk : LipschitzWith k V) (hl : ∀ x, ‖V x‖ ≤ l)
    (hK : LipschitzWith K W) (hL : ∀ y, ‖W y‖ ≤ L)
    (hVs : tsupport V ⊆ e.source)
    (hpush : ∀ x ∈ e.source, W (e x) = fderiv ℝ e x (V x))
    {x : E} (hx : x ∈ e.source) (t : ℝ) :
    boundedFlow W hK hL (e x) t = e (boundedFlow V hk hl x t) := by
  have hmem (s : ℝ) : boundedFlow V hk hl x s ∈ e.source :=
    boundedFlow_mapsTo_set V hk hl
      (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hVs h))) s hx
  have hd (s : ℝ) : HasDerivAt (fun v => e (boundedFlow V hk hl x v))
      (W (e (boundedFlow V hk hl x s))) s := by
    rw [hpush _ (hmem s)]
    have hdif := (he.contDiffAt (e.open_source.mem_nhds (hmem s))).differentiableAt
      (by simp)
    exact hdif.hasFDerivAt.comp_hasDerivAt s (boundedFlow_hasDerivAt V hk hl x s)
  have heq := boundedField_solution_unique W hK
    (boundedFlow_hasDerivAt W hK hL (e x)) hd (by rw [boundedFlow_zero, boundedFlow_zero])
  exact congrFun heq t

end PoincareConjecture.M25.Topology3D
