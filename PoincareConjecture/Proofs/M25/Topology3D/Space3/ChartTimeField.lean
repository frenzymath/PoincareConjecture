import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldChartTransport
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def chartTimeField (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (p : ℝ × E) : E := (fderiv ℝ e (e.symm p) (1, 0)).2

theorem chartTimeField_contDiffOn (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (chartTimeField e) e.target := by
  exact (((he.fderiv_of_isOpen e.open_source (by simp)).comp hi
    (fun _ hp => e.map_target hp)).clm_apply contDiffOn_const).snd

theorem chartTimeField_track (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (he : ContDiffOn ℝ ∞ e e.source)
    (htime : ∀ p ∈ e.source, (e p).1 = p.1)
    (t : ℝ) (x : E) (hp : (t, x) ∈ e.source) :
    HasDerivAt (fun s => (e (s, x)).2) (chartTimeField e (t, (e (t, x)).2)) t := by
  have hd := (he.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt (by simp)
  have hc : HasDerivAt (fun s => e (s, x)) (fderiv ℝ e (t, x) (1, 0)) t := by
    simpa only [Function.comp_def, id_eq] using hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hpair : (t, (e (t, x)).2) = e (t, x) := Prod.ext (htime _ hp).symm rfl
  rw [hpair, chartTimeField, e.left_inv hp]
  exact hc.snd

theorem chartTimeField_preserves_linear (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (he : ContDiffOn ℝ ∞ e e.source) (A : E →L[ℝ] F)
    (hA : ∀ p ∈ e.source, A (e p).2 = A p.2)
    (p : ℝ × E) (hp : p ∈ e.target) : A (chartTimeField e p) = 0 := by
  have hz := e.map_target hp
  have hd := (he.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt (by simp)
  let L := A.comp (ContinuousLinearMap.snd ℝ ℝ E)
  have heq : (fun z : ℝ × E => A (e z).2) =ᶠ[𝓝 (e.symm p)] fun z => A z.2 := by
    filter_upwards [e.open_source.mem_nhds hz] with z hzs
    exact hA z hzs
  have hleft : HasFDerivAt (fun z : ℝ × E => A (e z).2)
      (L.comp (fderiv ℝ e (e.symm p))) (e.symm p) :=
    L.hasFDerivAt.comp _ hd.hasFDerivAt
  have hright : HasFDerivAt (fun z : ℝ × E => A (e z).2) L (e.symm p) :=
    L.hasFDerivAt.congr_of_eventuallyEq heq
  have heval := congrArg (fun M : (ℝ × E) →L[ℝ] F => M (1, 0)) (hleft.unique hright)
  change A (chartTimeField e p) = A (0 : E) at heval
  simpa only [map_zero] using heval

end PoincareConjecture.M25.Topology3D
