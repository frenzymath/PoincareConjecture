import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Joint continuity of uniformly controlled inverse families

A uniform inverse distance bound transfers joint continuity
to inverses. This supplies the isotopy condition for the small
supported deformations in Alexander 1924, p. 7 and M76
derivation 143.
-/

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace Homeomorph

/-- Jointly continuous homeomorphisms with one uniform inverse
distance bound have jointly continuous inverses. No compactness
of the parameter or ambient spaces is needed. See derivation 143. -/
theorem continuous_symm_family_of_antilipschitz {T X Y : Type*}
    [TopologicalSpace T] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (H : T → X ≃ₜ Y) (hH : Continuous (fun p : T × X => H p.1 p.2))
    {K : ℝ≥0} (hK : ∀ t, AntilipschitzWith K (H t)) :
    Continuous (fun p : T × Y => (H p.1).symm p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let x : X := (H p.1).symm p.2
  have hc : Continuous (fun q : T × Y => (K : ℝ) * dist q.2 (H q.1 x)) :=
    continuous_const.mul (continuous_snd.dist (hH.comp (continuous_fst.prodMk continuous_const)))
  have ht : Tendsto (fun q : T × Y => (K : ℝ) * dist q.2 (H q.1 x)) (𝓝 p) (𝓝 0) := by
    simpa [x] using hc.continuousAt.tendsto (x := p)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) ?_ ht
  intro q
  simpa only [Homeomorph.apply_symm_apply] using (hK q.1).le_mul_dist ((H q.1).symm q.2) x

end Homeomorph
