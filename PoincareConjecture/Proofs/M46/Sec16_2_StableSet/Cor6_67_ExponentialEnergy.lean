import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_InitialBound
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVector










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}




theorem exponential_square_energy_uniform_bound
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x)
    {F0 : Set G.Point} {delta H D CR Cgrad : ℝ}
    (hdelta : 0 < delta) (hD : 0 ≤ D) (hCR : 0 ≤ CR) (hCgrad : 0 ≤ Cgrad)
    (hRic : ∀ q ∈ F0, ∀ v w : G.Horizontal q, |horizontalRicci G.leafwise q v w| ≤
      CR * Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
        Real.sqrt (G.spacetime.horizontalMetric.inner q w w))
    (hgrad : ∀ q ∈ F0, ∀ v : G.Horizontal q,
      |M14HorizontalScalarDifferential G q v.val| ≤
        Cgrad * Real.sqrt (G.spacetime.horizontalMetric.inner q v v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z : G.Horizontal x, ∀ s : ℝ,
      ∀ hlower : delta ≤ s, s ≤ H → ∀ hs : (Z, s) ∈ E.domain,
      E.action Z s ≤ D → (∀ r ∈ Icc 0 s, E.gamma Z r ∈ F0) →
      ∀ r ∈ Icc 0 s,
        G.spacetime.horizontalMetric.inner
          ((E.square_path Z s hs (hdelta.trans_le hlower)).curve r)
          ((E.square_path Z s hs (hdelta.trans_le hlower)).horizontal_velocity r)
          ((E.square_path Z s hs (hdelta.trans_le hlower)).horizontal_velocity r) ≤ C := by
  let A := 2 * H ^ 2 * Cgrad + 4 * H * CR
  let B := Real.exp (A * H) * (2 * D + 4 * ((n : ℝ) * CR) * H ^ 3 + H)
  let C := (Real.sqrt (B / delta + 4 * H ^ 2)) ^ 2
  refine ⟨C, sq_nonneg _, ?_⟩
  intro Z s hlower hupper hs haction hconf r hr
  have hpos : 0 < s := hdelta.trans_le hlower
  let R := E.square_path Z s hs hpos
  have hinterval : M14SqrtParameterInterval 0 (s ^ 2) = Icc 0 s := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le]
  have hconfR (a : ℝ) (ha : a ∈ M14SqrtParameterInterval 0 (s ^ 2)) : R.curve a ∈ F0 := by
    rw [M14.exponential_square_curve_eq E Z hs hpos ha]
    exact hconf a (hinterval ▸ ha)
  have henergy := M14.squareRoot_energy_uniform_bound hM12 R (E.square_extension Z s hs hpos)
    (E.square_euler Z s hs hpos) hdelta
    (by simpa only [Real.sqrt_sq hpos.le] using hlower)
    (by simpa only [Real.sqrt_sq hpos.le] using hupper) hCR hCgrad hD
    (by simpa only [← E.action_eq Z s hs hpos] using haction)
    (fun a ha => hRic _ (hconfR a ha))
    (fun a ha => hgrad _ (hconfR a ha)) (hinterval.symm ▸ hr)
  change G.spacetime.horizontalMetric.inner (R.curve r)
    (R.horizontal_velocity r) (R.horizontal_velocity r) + 4 * r ^ 2 ≤ C at henergy
  nlinarith [sq_nonneg r]

end PoincareConjecture.Proofs.M46
