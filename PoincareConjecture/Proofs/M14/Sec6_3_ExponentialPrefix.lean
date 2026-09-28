import PoincareConjecture.Proofs.M14.Sec6_3_PrefixUniqueness
import PoincareConjecture.Definitions.M14Exponential









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point}

private theorem exists_uniqueMinimizing_prefix
    (hM04 : RicciFlowCurvatureTheory.{0}) (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T a b x y) (hq : M14IsMinimizing q)
    (hac : a < c) (hcb : c < b) {z : G.Point} (hz : q.curve c = z) :
    ∃ p : M14BackwardPath G T a c x z, EqOn p.curve q.curve (Icc a c) ∧
      M14IsMinimizing p ∧ ∀ r : M14BackwardPath G T a c x z,
        M14IsMinimizing r → EqOn r.curve p.curve (Icc a c) := by
  subst z
  refine ⟨prefixPath q c hac hcb.le, fun _ _ => rfl,
    isMinimizing_prefixPath hM12 q hq ⟨hac, hcb⟩, ?_⟩
  intro r hr
  exact minimizing_prefix_eqOn hM04 hCoordinates hM12 q hq r hr hcb




theorem uniqueMinimizingBranch_of_minimizing_extension
    (hM04 : RicciFlowCurvatureTheory.{0}) (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) (q : M14BackwardPath G T 0 b x y) (hq : M14IsMinimizing q)
    (hc : 0 < c) (hcb : c < b) (hD : (Z, Real.sqrt c) ∈ E.domain)
    (hcurve : EqOn q.curve (fun t => E.gamma Z (Real.sqrt t)) (Icc 0 b)) :
    M14UniqueMinimizingBranch G T c x E Z := by
  obtain ⟨p, hpcurve, hpmin, hpuniq⟩ := exists_uniqueMinimizing_prefix hM04 hCoordinates hM12
    q hq hc hcb (hcurve ⟨hc.le, hcb.le⟩)
  refine ⟨hD, p, ?_, hpmin, hpuniq⟩
  intro t ht
  exact (hpcurve ht).trans (hcurve ⟨ht.1, ht.2.trans hcb.le⟩)



theorem uniqueMinimizingBranch_prefix
    (hM04 : RicciFlowCurvatureTheory.{0}) (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} (hc : 0 < c) (hcb : c < b)
    (hbranch : M14UniqueMinimizingBranch G T b x E Z) :
    M14UniqueMinimizingBranch G T c x E Z := by
  obtain ⟨hDb, q, hcurve, hmin, _⟩ := hbranch
  have hDc : (Z, Real.sqrt c) ∈ E.domain :=
    (E.maximal_lifetime Z).out (E.domain_zero Z) hDb
      ⟨Real.sqrt_nonneg c, Real.sqrt_le_sqrt hcb.le⟩
  exact uniqueMinimizingBranch_of_minimizing_extension hM04 hCoordinates hM12
    E Z q hmin hc hcb hDc hcurve

end PoincareConjecture.M14
