import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoordinateJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Connection.JetBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds CoordinateExponential

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

theorem exists_uniform_comparisonChristoffel_bound
    (q : ℕ) {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : RiemannianMetric 3 E) (x : E),
      (∀ v : E, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
      (∀ j ≤ q + 1, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ B) →
      ∀ j ≤ q, ∀ b c d : Fin 3,
        ‖iteratedFDeriv ℝ j (comparisonChristoffel g b c d) x‖ ≤ C := by
  let D := max B 1
  have hD : 1 ≤ D := le_max_right _ _
  obtain ⟨C, hC, hbound⟩ := @exists_uniform_christoffel_jet_bound
    (EuclideanSpace ℝ (Fin 3)) _ _ _ q a ha B D hD
  refine ⟨C, hC, ?_⟩
  intro g x hell hjets j hj b c d
  have hzero := hjets 0 (by omega)
  rw [norm_iteratedFDeriv_zero] at hzero
  have hmetric (l : ℕ) (hl : 1 ≤ l) (hlq : l ≤ q + 1) :
      ‖iteratedFDeriv ℝ l g.euclideanCoefficients x‖ ≤ D ^ l :=
    (hjets l hlq).trans ((le_max_left _ _).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hD hl))
  have h := hbound g.euclideanCoefficients x (g.contDiffAt_euclideanCoefficients x)
    hzero hell hmetric j hj (e c) (e d)
  have hcoeff : ContDiffAt ℝ ∞
      (fun y => christoffelBilinear g.euclideanCoefficients y (e c) (e d)) x :=
    ((contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
      (g.inner_isInvertible x)).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hcomp := norm_iteratedFDeriv_inner_le hcoeff j (le_of_eq ((e).norm_eq_one b))
  exact hcomp.trans (by simpa only [(e).norm_eq_one, mul_one] using h)

theorem exists_uniform_bilinear_error_jet_bound
    (j : ℕ) {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
      (A : E → E →L[ℝ] E →L[ℝ] ℝ) (U : Set E),
      IsOpen U → ContDiffOn ℝ ∞ A U →
      ∀ rho : ℝ, 0 ≤ rho → ∀ x : E, x ∈ U →
      (∀ v : E, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
      (∀ m ≤ j + 1, ‖iteratedFDeriv ℝ m g.euclideanCoefficients x‖ ≤ B) →
      (∀ b : Fin 3, g.tangentNorm x (e b) ≤ L) →
      (∀ m ≤ j, g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => A y (v 0) (v 1) - g.inner y (v 0) (v 1)) m) x ≤ rho) →
      ‖iteratedFDeriv ℝ j (A - g.euclideanCoefficients) x‖ ≤ C * rho := by
  obtain ⟨G, hG, hchrist⟩ := exists_uniform_comparisonChristoffel_bound j ha B
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_local_bilinear_jet_bound_of_covariant_norms (fun _ => G)
      (fun _ => hG) hL j
  refine ⟨C, hC, ?_⟩
  intro g D A U hU hA rho hrho x hx hell hjets hframe hnorm
  exact hbound D A U hU hA rho hrho x hx hframe (hchrist g x hell hjets) hnorm

end PoincareConjecture.M44
