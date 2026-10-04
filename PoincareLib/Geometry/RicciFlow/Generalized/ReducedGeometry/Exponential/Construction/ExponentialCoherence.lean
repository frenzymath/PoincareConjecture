import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialAction

/-!
# Every supplied exponential family agrees with the actual IVP

Morgan-Tian Definition 6.17 and Lemma 6.18, pp. 113-114.
The frozen family's path and square Euler data are an actual normalized
IVP. Its survival characterization and the proved actual uniqueness
identify its domain, curve, and positive-time action with the canonical
family. No off-domain or zero-time action is prescribed.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The supplied family's path is itself the normalized actual IVP,
Definition 6.17 and Lemma 6.18, pp. 113-114. -/
def exponentialInitialValuePath (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    M14SquareRootInitialValuePath G T (s ^ 2) x (E.gamma Z s) Z where
  path := E.path Z s hs hpos
  square_path := E.square_path Z s hs hpos
  extension := E.square_extension Z s hs hpos
  euler := E.square_euler Z s hs hpos
  initial_velocity := E.square_initial_velocity Z s hs hpos

/-- Every supplied exponential family has precisely the actual IVP
survival domain, including all initial vectors at time zero,
Definition 6.17 and Lemma 6.18, pp. 113-114. -/
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

/-- The supplied and canonical exponential curves agree everywhere
on their common actual survival domain, Lemma 6.18, pp. 113-114. -/
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

/-- Positive-time supplied action is exactly the canonical actual
IVP action; the arbitrary zero-time convention is not used,
equation (6.2) and Lemma 6.18, pp. 106, 113-114. -/
theorem exponentialFamily_action_eq
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    E.action Z s = initialValueAction G T x Z s :=
  (E.action_eq Z s hs hpos).trans
    (initialValueAction_eq_of_path hM04 hM12 hpos
      (exponentialInitialValuePath E Z s hs hpos)).symm

end PoincareMT.M14
