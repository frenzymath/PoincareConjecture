import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.CurvatureNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem self_first_zero (D : LeviCivitaData g) (x : M)
    (u w z : TangentSpace (𝓡 n) x) : D.curvatureTensor x u u w z = 0 := by
  linarith only [D.curvatureTensor_swap_first x u u w z]

private theorem zero_first (D : LeviCivitaData g) (x : M)
    (u w z : TangentSpace (𝓡 n) x) : D.curvatureTensor x 0 u w z = 0 := by
  simpa only [zero_smul, zero_mul] using D.curvatureTensor_smul_first x 0 u u w z

private theorem positive_plane_coefficients (D : LeviCivitaData g) (x : M)
    (u w : TangentSpace (𝓡 n) x) (hpos : 0 < D.curvatureTensor x u w u w)
    (a b : ℝ)
    (ha : D.curvatureTensor x (a • u + b • w) w u w = 0)
    (hb : D.curvatureTensor x (a • u + b • w) u u w = 0) : a = 0 ∧ b = 0 := by
  have ha0 : a = 0 := by
    have hh : a * D.curvatureTensor x u w u w = 0 := by
      simpa only [D.curvatureTensor_add_first, D.curvatureTensor_smul_first,
        self_first_zero, mul_zero, add_zero] using ha
    exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt hpos)
  have hb0 : b = 0 := by
    have hh : b * (-D.curvatureTensor x u w u w) = 0 := by
      simpa only [D.curvatureTensor_add_first, D.curvatureTensor_smul_first,
        self_first_zero, mul_zero, zero_add, D.curvatureTensor_swap_first x w u u w]
        using hb
    exact (mul_eq_zero.mp hh).resolve_right (neg_ne_zero.mpr (ne_of_gt hpos))
  exact ⟨ha0, hb0⟩


theorem terminalCurvature_null_not_mem_positive_plane
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x u w u w)
    (v u w : TangentSpace (𝓡 n) x) (hv : v ≠ 0) (hnull : D.ricci x v v = 0)
    (hpos : 0 < D.curvatureTensor x u w u w) :
    v ∉ Submodule.span ℝ ({u, w} : Set (TangentSpace (𝓡 n) x)) := by
  rintro hmem
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  have hzero := RicciFlow.Splitting.curvatureTensor_eq_zero_of_ricci_self_eq_zero
    D hD x hsec hnull
  have hc := positive_plane_coefficients D x u w hpos a b
    (by rw [hab]; exact hzero w u w) (by rw [hab]; exact hzero u u w)
  apply hv
  simp only [← hab, hc.1, hc.2, zero_smul, zero_add]



theorem terminalCurvature_positive_plane_transverse
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x u w u w)
    (L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) (hv : v ≠ 0) (hnull : D.ricci x v v = 0)
    (hplane : ∃ a b, 0 < D.curvatureTensor x (L a) (L b) (L a) (L b)) :
    Function.Injective L ∧ v ∉ range L := by
  obtain ⟨a, b, hab⟩ := hplane
  have hLI : LinearIndependent ℝ ![L a, L b] := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro hb
      have heq : L b = 0 := hb
      have hc := positive_plane_coefficients D x (L a) (L b) hab 0 1
        (by simp only [zero_smul, one_smul, zero_add, heq]; exact zero_first D x _ _ _)
        (by simp only [zero_smul, one_smul, zero_add, heq]; exact zero_first D x _ _ _)
      norm_num at hc
    · intro c hc
      have heq : c • L b = L a := hc
      have hz : (1 : ℝ) • L a + (-c) • L b = 0 := by
        rw [one_smul, ← heq, neg_smul, add_neg_cancel]
      have hcoef := positive_plane_coefficients D x (L a) (L b) hab 1 (-c)
        (by rw [hz]; exact zero_first D x _ _ _) (by rw [hz]; exact zero_first D x _ _ _)
      norm_num at hcoef
  have hsource : LinearIndependent ℝ ![a, b] := by
    apply LinearIndependent.of_comp L
    have heq : L ∘ ![a, b] = ![L a, L b] := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact hLI
  have hspan : Submodule.span ℝ ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
    simpa only [Matrix.range_cons_cons_empty] using
      hsource.span_eq_top_of_card_eq_finrank (by simp)
  have hrepr (z : EuclideanSpace ℝ (Fin 2)) : ∃ c d : ℝ, c • a + d • b = z := by
    apply Submodule.mem_span_pair.mp
    rw [hspan]
    trivial
  constructor
  · apply (injective_iff_map_eq_zero L).mpr
    intro z hz
    obtain ⟨c, d, rfl⟩ := hrepr z
    have hh : c • L a + d • L b = 0 := by simpa only [map_add, map_smul] using hz
    have hc := positive_plane_coefficients D x (L a) (L b) hab c d
      (by rw [hh]; exact zero_first D x _ _ _) (by rw [hh]; exact zero_first D x _ _ _)
    simp only [hc.1, hc.2, zero_smul, zero_add]
  · rintro ⟨z, hz⟩
    apply terminalCurvature_null_not_mem_positive_plane D hD x hsec v (L a) (L b)
      hv hnull hab
    obtain ⟨c, d, rfl⟩ := hrepr z
    apply Submodule.mem_span_pair.mpr
    exact ⟨c, d, by simpa only [map_add, map_smul] using hz⟩

end PoincareConjecture.M47
