import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.RicciQuadratic
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.GramDerivative
import PoincareConjecture.Proofs.M60.Mathlib.GramTraceBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem m60SphereRicciTraceDensity_bound (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) {C : ℝ} (hC : 0 ≤ C)
    (hnorm : ∀ x : M, D.ricciNormSq x ≤ C ^ 2)
    (f : UnitTwoSphere → M) (z : LoopPlane) :
    |m60SphereRicciTraceDensity D f z| ≤ 4 * C * m60SphereAreaDensity g f z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let x := (f ∘ m60SphereParameter) z
  let v := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 n) (f ∘ m60SphereParameter) z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have harea : 0 ≤ m60SphereAreaDensity g f z :=
    m60AreaDensity_nonneg g (f ∘ m60SphereParameter) z
  by_cases hdeg : Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z) = 0
  · rw [m60SphereRicciTraceDensity_eq_zero D f z hdeg, abs_zero]
    positivity
  have hpos : 0 < Matrix.det (Matrix.gram ℝ v) :=
    lt_of_le_of_ne (m60AreaGram_det_nonneg g (f ∘ m60SphereParameter) z) (Ne.symm hdeg)
  obtain ⟨B, hB⟩ := m60Ricci_exists_bilinear D hD x
  have hbound (w : TangentSpace (𝓡 n) x) : |B w w| ≤ C * inner ℝ w w := by
    rw [hB]
    exact m60Ricci_quadratic_bound D hD x hC (hnorm x) w
  have htrace : |∑ i : Fin 2, ∑ j : Fin 2,
      ((m60AreaGram g (f ∘ m60SphereParameter) z)⁻¹) i j * D.ricci x (v j) (v i)| ≤ 2 * C := by
    have h := M60.abs_inverse_gram_contraction_le v B hbound hpos
    change |∑ i : Fin 2, ∑ j : Fin 2,
      ((m60AreaGram g (f ∘ m60SphereParameter) z)⁻¹) i j * B (v j) (v i)| ≤ 2 * C at h
    simp_rw [hB] at h
    exact h
  change 0 ≤ m60AreaDensity g (f ∘ m60SphereParameter) z at harea
  unfold m60SphereRicciTraceDensity
  rw [if_neg hdeg, abs_mul, abs_of_nonneg harea]
  exact (mul_le_mul_of_nonneg_right htrace harea).trans
    (mul_le_mul_of_nonneg_right (by linarith : 2 * C ≤ 4 * C) harea)

end PoincareConjecture
