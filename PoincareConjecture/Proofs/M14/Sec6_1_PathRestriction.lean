import PoincareConjecture.Proofs.M14.Sec6_1_LLength

set_option autoImplicit false

open scoped intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

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

theorem action_restrictPath (p : M14BackwardPath G T τ₁ τ₂ x y)
    (a b : ℝ) (ha : τ₁ ≤ a) (hab : a < b) (hb : b ≤ τ₂) :
    M14BackwardLAction G (restrictPath p a b ha hab hb) =
      ∫ t in a..b, M14BackwardLIntegrand G p t := rfl

theorem action_split (p : M14BackwardPath G T τ₁ τ₂ x y)
    {a : ℝ} (ha : a ∈ Set.Ioo τ₁ τ₂) :
    M14BackwardLAction G (restrictPath p τ₁ a le_rfl ha.1 ha.2.le) +
        M14BackwardLAction G (restrictPath p a τ₂ ha.1.le ha.2 le_rfl) =
      M14BackwardLAction G p := by
  exact intervalIntegral.integral_add_adjacent_intervals
    (restrictPath p τ₁ a le_rfl ha.1 ha.2.le).action_integrable
    (restrictPath p a τ₂ ha.1.le ha.2 le_rfl).action_integrable

end PoincareConjecture.M14
