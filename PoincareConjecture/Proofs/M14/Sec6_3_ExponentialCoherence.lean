import PoincareConjecture.Proofs.M14.Sec6_3_InitialAction











set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}



def exponentialInitialValuePath (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    M14SquareRootInitialValuePath G T (s ^ 2) x (E.gamma Z s) Z where
  path := E.path Z s hs hpos
  square_path := E.square_path Z s hs hpos
  extension := E.square_extension Z s hs hpos
  euler := E.square_euler Z s hs hpos
  initial_velocity := E.square_initial_velocity Z s hs hpos




theorem exponentialFamily_domain_eq (E : M14ExponentialFamily G T x) :
    E.domain = initialValueDomain G T x := by
  ext ⟨Z, s⟩
  constructor
  · intro hs
    rcases eq_or_lt_of_le (E.domain_admissible hs).1 with hzero | hpos
    · change 0 = s at hzero
      subst s
      exact initialValueDomain_zero Z
    · exact (initialValueDomain_positive_iff hpos).mpr
        ((E.positive_survival_iff Z s hpos).mp hs)
  · intro hs
    rcases eq_or_lt_of_le (initialValueDomain_nonneg hs) with hzero | hpos
    · subst s
      exact E.domain_zero Z
    · exact (E.positive_survival_iff Z s hpos).mpr
        ((initialValueDomain_positive_iff hpos).mp hs)



theorem exponentialFamily_gamma_eq
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) : E.gamma Z s = initialValueCurve G T x Z s := by
  rcases eq_or_lt_of_le (E.domain_admissible hs).1 with hzero | hpos
  · change 0 = s at hzero
    subst s
    exact (E.gamma_at_zero Z).trans (initialValueCurve_zero Z).symm
  · exact (initialValueCurve_eq_endpoint hM04 hM12 hpos
      (exponentialInitialValuePath E Z s hs hpos)).symm




theorem exponentialFamily_action_eq
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    E.action Z s = initialValueAction G T x Z s :=
  (E.action_eq Z s hs hpos).trans
    (initialValueAction_eq_of_path hM04 hM12 hpos
      (exponentialInitialValuePath E Z s hs hpos)).symm

end PoincareConjecture.M14
