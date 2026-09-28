import PoincareConjecture.Proofs.M14.Sec6_3_CornerVelocity
import PoincareConjecture.Proofs.M14.Sec6_3_EulerUnique
import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerEuler
import PoincareConjecture.Proofs.M14.Sec6_2_EulerEquation










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point}




theorem minimizing_prefix_eqOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T a b x y) (hq : M14IsMinimizing q)
    (p : M14BackwardPath G T a c x (q.curve c)) (hp : M14IsMinimizing p) (hc : c < b) :
    EqOn p.curve q.curve (Icc a c) := by
  have hprefix := isMinimizing_prefixPath hM12 q hq ⟨p.tau_lt, hc⟩
  have haction : M14BackwardLAction G p =
      M14BackwardLAction G (prefixPath q c p.tau_lt hc.le) :=
    le_antisymm (hp _) (hprefix p)
  obtain ⟨Ep₀, hEp₀⟩ := minimizerEulerStatement hCoordinates hM12 T a c x (q.curve c) p hp
  obtain ⟨Eq₀, hEq₀⟩ := minimizerEulerStatement hCoordinates hM12 T a b x y q hq
  obtain ⟨Rp, Ep, hEp⟩ := squareRootRegularizationStatement hCoordinates hM12
    T a c x (q.curve c) p Ep₀ hEp₀
  obtain ⟨Rq, Eq, hEq⟩ := squareRootRegularizationStatement hCoordinates hM12
    T a b x y q Eq₀ hEq₀
  have hvel := squareVelocity_eq_of_minimizing_corner hCoordinates hM12
    q hq p hc haction Rp Rq Ep Eq hEp hEq
  have hsub : M14SqrtParameterInterval a c ⊆ M14SqrtParameterInterval a b :=
    Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hc.le)
  have hs : Real.sqrt c ∈ M14SqrtParameterInterval a c :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hpoint : Rp.curve (Real.sqrt c) = Rq.curve (Real.sqrt c) := by
    rw [Rp.agrees _ hs, Rq.agrees _ (hsub hs),
      Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), p.curve_end]
  have hsame := squareRootEuler_unique hM04 hM12 Rp Rq
    (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) Subset.rfl hsub Ep Eq hEp
    (fun s hs => hEq s (hsub hs)) hs hpoint hvel
  intro t ht
  have hsqrt : Real.sqrt t ∈ M14SqrtParameterInterval a c :=
    ⟨Real.sqrt_le_sqrt ht.1, Real.sqrt_le_sqrt ht.2⟩
  calc
    p.curve t = Rp.curve (Real.sqrt t) := by
      rw [Rp.agrees _ hsqrt, Real.sq_sqrt (p.tau_nonneg.trans ht.1)]
    _ = Rq.curve (Real.sqrt t) := (hsame _ hsqrt).1
    _ = q.curve t := by
      rw [Rq.agrees _ (hsub hsqrt), Real.sq_sqrt (p.tau_nonneg.trans ht.1)]

end PoincareConjecture.M14
