import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_PositiveAction
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration
import PoincareConjecture.Proofs.M14.Sec6_1_PathPrefix









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



theorem prefix_action_le_scalar_floor_correction {T S tau : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 S x y) (htau : 0 < tau) (htauS : tau ≤ S)
    (hscalar : ∀ s ∈ Icc 0 S,
      -6 ≤ horizontalScalarCurvature G.leafwise (p.curve s)) :
    M14BackwardLAction G (M14.prefixPath p tau htau htauS) ≤
      M14BackwardLAction G p + 4 * S * Real.sqrt S := by
  let f s := M14BackwardLIntegrand G p s + 6 * Real.sqrt s
  have hroot : IntervalIntegrable (fun s : ℝ => 6 * Real.sqrt s) volume 0 S :=
    (Real.continuous_sqrt.const_mul 6).intervalIntegrable _ _
  have hf : IntervalIntegrable f volume 0 S := p.action_integrable.add hroot
  have hsub : uIcc 0 tau ⊆ uIcc 0 S := by
    rw [uIcc_of_le htau.le, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc_right htauS
  have hnonneg (s : ℝ) (hs : s ∈ Icc 0 S) : 0 ≤ f s := by
    have hkin : 0 ≤ G.spacetime.horizontalMetric.inner (p.curve s)
        (p.horizontal_velocity s) (p.horizontal_velocity s) :=
      (G.spacetime.horizontalMetric.toRiemannianMetric.toCore
        (p.curve s)).re_inner_nonneg (p.horizontal_velocity s)
    have hsum : 0 ≤ horizontalScalarCurvature G.leafwise (p.curve s) +
        G.spacetime.horizontalMetric.inner (p.curve s)
          (p.horizontal_velocity s) (p.horizontal_velocity s) + 6 := by
      linarith [hscalar s hs]
    have h := mul_nonneg (Real.sqrt_nonneg s) hsum
    dsimp only [f, M14BackwardLIntegrand, M14RawLIntegrand]
    nlinarith
  have hprefix : (∫ s in (0 : ℝ)..tau, M14BackwardLIntegrand G p s) ≤
      ∫ s in (0 : ℝ)..tau, f s :=
    intervalIntegral.integral_mono_on htau.le (p.action_integrable.mono_set hsub)
      (hf.mono_set hsub) (fun s _ => by
        dsimp only [f]
        exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.sqrt_nonneg s)))
  have hwhole := intervalIntegral.integral_mono_interval le_rfl htau.le htauS
    ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all volume (fun s hs => hnonneg s ⟨hs.1.le, hs.2⟩))) hf
  have hvalue : (∫ s in (0 : ℝ)..S, f s) =
      M14BackwardLAction G p + 4 * S * Real.sqrt S := by
    change (∫ s in (0 : ℝ)..S,
      M14RawLIntegrand G p.curve p.horizontal_velocity s + 6 * Real.sqrt s) = _
    rw [intervalIntegral.integral_add p.action_integrable hroot,
      intervalIntegral.integral_const_mul, integral_sqrt_nonneg_endpoint p.tau_lt.le]
    change M14BackwardLAction G p + 6 * ((2 / 3 : ℝ) * S * Real.sqrt S) = _
    ring
  exact hprefix.trans (hvalue ▸ hwhole)



theorem prefix_action_budget_margin {K : MetricSurgeryConstants}
    (prefixData : SurgeryParameterPrefix K) {T S tau : ℝ} {x y : G.Point}
    (path : M14BackwardPath G T 0 S x y) (htau : 0 < tau) (htauS : tau ≤ S)
    (hS : S ≤ surgeryEpochStart (prefixData.i + 1))
    (hscalar : ∀ s ∈ Icc 0 S,
      -6 ≤ horizontalScalarCurvature G.leafwise (path.curve s))
    (hshort : M14BackwardLAction G path ≤ 3 * Real.sqrt S) :
    M14BackwardLAction G (M14.prefixPath path tau htau htauS) ≤
      actionBudget prefixData / 2 - Real.sqrt (surgeryEpochStart (prefixData.i + 1)) := by
  have hroot := Real.sqrt_le_sqrt hS
  have hprod := mul_le_mul hS hroot (Real.sqrt_nonneg S)
    (path.tau_lt.le.trans hS)
  have hbound := prefix_action_le_scalar_floor_correction path htau htauS hscalar
  unfold actionBudget
  nlinarith

end PoincareConjecture.Proofs.M46
