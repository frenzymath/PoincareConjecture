import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.RawMetricMaximum
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem metric_norm_bound_on_open_of_ae (g : RiemannianMetric n V)
    {O K : Set V} (hO : IsOpen O) (hOK : O ⊆ K) {Q : ℝ}
    (u : Lp V 2 (volume : Measure V)) (X : V → V) (hX : ContinuousOn X O)
    (hrep : X =ᵐ[volume.restrict O] u)
    (hb : ∀ᵐ x ∂volume, x ∈ K → g.inner x (u x) (u x) ≤ Q) :
    ∀ x ∈ O, g.inner x (X x) (X x) ≤ Q := by
  have hq : ContinuousOn (fun x => g.inner x (X x) (X x)) O :=
    (metric_quadratic_contDiff g).continuous.comp_continuousOn
      (continuous_id.continuousOn.prodMk hX)
  have he : (fun x => max (g.inner x (X x) (X x)) Q) =ᵐ[volume.restrict O] fun _ => Q := by
    filter_upwards [hrep, ae_restrict_of_ae hb, ae_restrict_mem hO.measurableSet]
      with x hx hb hxO
    exact max_eq_right (hx ▸ hb (hOK hxO))
  have hpoint := Measure.eqOn_open_of_ae_eq he hO (hq.sup continuous_const.continuousOn)
    continuous_const.continuousOn
  exact fun x hx => max_eq_right_iff.mp (hpoint hx)

end PoincareConjecture.M35.Uniqueness.Heat
