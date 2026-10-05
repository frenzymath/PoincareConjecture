import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.LLength

/-!
# Restricting an admissible generalized backward path

Morgan-Tian Definition 6.2, p. 106, and the action decomposition used in
Proposition 6.30, p. 118. Restriction preserves the actual curve and horizontal
velocity; it does not introduce a corner or assert prefix minimality.
-/

set_option autoImplicit false

open scoped intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

/-- Restrict a backward path to a nondegenerate closed subinterval, retaining
the absolute backward clock; Morgan-Tian Definition 6.2, p. 106. -/
def restrictPath (p : M14BackwardPath G T τ₁ τ₂ x y)
    (a b : ℝ) (ha : τ₁ ≤ a) (hab : a < b) (hb : b ≤ τ₂) :
    M14BackwardPath G T a b (p.curve a) (p.curve b) where
  tau_nonneg := p.tau_nonneg.trans ha
  tau_lt := hab
  base_time := p.curve_time a ⟨ha, hab.le.trans hb⟩
  endpoint_time := p.curve_time b ⟨ha.trans hab.le, hb⟩
  curve := p.curve
  curve_start := rfl
  curve_end := rfl
  curve_time := fun t ht => p.curve_time t ⟨ha.trans ht.1, ht.2.trans hb⟩
  curve_continuous := p.curve_continuous.mono
    (fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)
  curve_regular := p.curve_regular.mono
    (fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)
  horizontal_velocity := p.horizontal_velocity
  derivative_eq := fun t ht => p.derivative_eq t
    ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  action_integrable := p.action_integrable.mono_set (by
    rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le p.tau_lt.le]
    exact fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)

/-- Restricted action is the original density integrated over the subinterval,
Morgan-Tian Definition 6.2, p. 106. -/
theorem action_restrictPath (p : M14BackwardPath G T τ₁ τ₂ x y)
    (a b : ℝ) (ha : τ₁ ≤ a) (hab : a < b) (hb : b ≤ τ₂) :
    M14BackwardLAction G (restrictPath p a b ha hab hb) =
      ∫ t in a..b, M14BackwardLIntegrand G p t := rfl

/-- Actions add exactly when an admissible path is split at an interior time,
as used in Morgan-Tian Proposition 6.30, p. 118. -/
theorem action_split (p : M14BackwardPath G T τ₁ τ₂ x y)
    {a : ℝ} (ha : a ∈ Set.Ioo τ₁ τ₂) :
    M14BackwardLAction G (restrictPath p τ₁ a le_rfl ha.1 ha.2.le) +
        M14BackwardLAction G (restrictPath p a τ₂ ha.1.le ha.2 le_rfl) =
      M14BackwardLAction G p := by
  exact intervalIntegral.integral_add_adjacent_intervals
    (restrictPath p τ₁ a le_rfl ha.1 ha.2.le).action_integrable
    (restrictPath p a τ₂ ha.1.le ha.2 le_rfl).action_integrable

end PoincareMT.M14
