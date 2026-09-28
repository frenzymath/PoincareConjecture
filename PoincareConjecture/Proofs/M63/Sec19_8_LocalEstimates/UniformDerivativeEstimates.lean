import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ProductSmallTurningCurvature
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ProductInverseAgeJetBounds











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : Nat} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : Real}




theorem m63UniformDerivativeEstimates_of_compact
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (hM62 : M62CurveEvolutionTheory.{u}) (G : M63AmbientGeometry F)
    (L0 Theta0 : Real) (hL0 : 0 ≤ L0) (hTheta0 : 0 ≤ Theta0) :
    Nonempty (M63UniformDerivativeEstimates G L0 Theta0) := by
  obtain ⟨delta, hdelta, hdelta1, hcurvature⟩ :=
    m63CircleProduct_small_turning_curvature F hcompact hM62 G L0 Theta0 hL0 hTheta0
  obtain ⟨C, hC, hjet⟩ :=
    m63CircleProduct_curvatureJetSquared_bound_of_inverse_age F hcompact G
  refine ⟨{
    delta0 := delta
    delta0_positive := hdelta
    delta0_lt_one := hdelta1
    radius0 := 1
    radius0_positive := by norm_num
    radius0_le_one := le_rfl
    constant := C
    constant_nonnegative := hC
    local_curvature := hcurvature
    all_derivatives := ?_ }⟩
  simp only [one_pow, mul_one]
  intro circumference hcirc hcirc1 c hc hL hTheta s r hs hr hr1 hEnd hLength hSmall t ht i x
  have hsT : s < s + delta * r ^ 2 :=
    lt_add_of_pos_right s (mul_pos hdelta (pow_pos hr 2))
  have hshort : s + delta * r ^ 2 - s ≤ 1 := by
    have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1.le
    have hm := mul_le_mul_of_nonneg_left hr2 hdelta.le
    linarith only [hm, hdelta1]
  have hzero := hcurvature circumference hcirc hcirc1 c hc hL hTheta s r hs hr hr1.le
    hEnd.le hLength hSmall
  exact hjet circumference hcirc c hc s (s + delta * r ^ 2) hs hsT hEnd.le hshort
    (fun u hu y => hzero u (Ioo_subset_Ioc_self hu) y) t ht i x

end PoincareConjecture
