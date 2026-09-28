import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurveEndpoints
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixMinimality
import PoincareConjecture.Proofs.M14.Sec6_1_PathCongruence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point}

theorem integral_squareCurveDensity_eq_action_of_curve
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (p : M14BackwardPath G T a b x y)
    (α : ℝ → G.Point)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b))
    (hclock : ∀ s ∈ M14SqrtParameterInterval a b,
      G.spacetime.timeFunction (α s) = T - s ^ 2)
    (heq : EqOn (fun t => α (Real.sqrt t)) p.curve (Icc a b)) :
    (∫ s in Real.sqrt a..Real.sqrt b, squareCurveDensity G α (M14SqrtParameterInterval a b) s) =
      M14BackwardLAction G p := by
  have hx : α (Real.sqrt a) = x := (heq ⟨le_rfl, p.tau_lt.le⟩).trans p.curve_start
  have hy : α (Real.sqrt b) = y := (heq ⟨p.tau_lt.le, le_rfl⟩).trans p.curve_end
  let q := backwardPathOfSquareCurveBetween hM12 p.tau_nonneg p.tau_lt α hα hclock hx hy
  exact (integral_squareCurveDensity_eq_action_between hM12 p.tau_nonneg p.tau_lt
    α hα Subset.rfl hclock hx hy).trans
      (action_eq_of_curve_eqOn q p (fun _ ht => heq (Ioo_subset_Icc_self ht)))

theorem minimizing_action_le_square_prefix_add_tail
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (m : M14BackwardPath G T a b x y) (hmin : M14IsMinimizing m) (hc : c ∈ Ioo a b)
    (α β : ℝ → G.Point)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b))
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (M14SqrtParameterInterval a b))
    (hαclock : ∀ s ∈ M14SqrtParameterInterval a b,
      G.spacetime.timeFunction (α s) = T - s ^ 2)
    (hβclock : ∀ s ∈ M14SqrtParameterInterval a b,
      G.spacetime.timeFunction (β s) = T - s ^ 2)
    (hαx : α (Real.sqrt a) = x) (hβx : β (Real.sqrt a) = x)
    (hβy : β (Real.sqrt b) = y) (hjoin : α (Real.sqrt c) = β (Real.sqrt c)) :
    M14BackwardLAction G m ≤
      (∫ s in Real.sqrt a..Real.sqrt c, squareCurveDensity G α (M14SqrtParameterInterval a b) s) +
      ∫ s in Real.sqrt c..Real.sqrt b, squareCurveDensity G β (M14SqrtParameterInterval a b) s := by
  have hpre : M14SqrtParameterInterval a c ⊆ M14SqrtParameterInterval a b :=
    fun _ hs => ⟨hs.1, hs.2.trans (Real.sqrt_le_sqrt hc.2.le)⟩
  have htail : M14SqrtParameterInterval c b ⊆ M14SqrtParameterInterval a b :=
    fun _ hs => ⟨(Real.sqrt_le_sqrt hc.1.le).trans hs.1, hs.2⟩
  let q := backwardPathOfSquareCurveBetween hM12 m.tau_nonneg m.tau_lt β hβ hβclock hβx hβy
  let p : M14BackwardPath G T a c x (q.curve c) :=
    backwardPathOfSquareCurveBetween hM12 m.tau_nonneg hc.1 α (hα.mono hpre)
      (fun s hs => hαclock s (hpre hs)) hαx hjoin
  have hA : (∫ s in Real.sqrt a..Real.sqrt c,
      squareCurveDensity G α (M14SqrtParameterInterval a b) s) = M14BackwardLAction G p :=
    integral_squareCurveDensity_eq_action_between hM12 m.tau_nonneg hc.1 α hα hpre
      (fun s hs => hαclock s (hpre hs)) hαx hjoin
  have hB : (∫ s in Real.sqrt c..Real.sqrt b,
      squareCurveDensity G β (M14SqrtParameterInterval a b) s) =
      ∫ t in c..b, M14BackwardLIntegrand G q t :=
    integral_squareCurveDensity_eq_action hM12 (m.tau_nonneg.trans hc.1.le) hc.2 β hβ htail
      (fun s hs => hβclock s (htail hs))
  rw [hA, hB]
  exact minimizing_action_le_prefix_add_tail hM12 m hmin q p hc.2

end PoincareConjecture.M14
