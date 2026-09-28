
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Barrier
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace











namespace Poincare.HamiltonIvey

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem rayleigh_ge_least {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = 3) {v : E} (hv : ‖v‖ = 1) :
    hT.eigenvalues hn 2 ≤ inner ℝ v (T v) := by
  have hexp : inner ℝ v (T v) =
      ∑ i, hT.eigenvalues hn i * (inner ℝ (hT.eigenvectorBasis hn i) v) ^ 2 := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map v (T v)]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, star_trivial,
      hT.eigenvectorBasis_apply_self_apply hn]
    simp only [(hT.eigenvectorBasis hn).repr_apply_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring
  have hsq : ∑ i, (inner ℝ (hT.eigenvectorBasis hn i) v) ^ 2 = 1 := by
    simpa [hv] using (hT.eigenvectorBasis hn).sum_sq_inner_right v
  rw [hexp]
  calc
    hT.eigenvalues hn 2 =
        ∑ i, hT.eigenvalues hn 2 * (inner ℝ (hT.eigenvectorBasis hn i) v) ^ 2 := by
      rw [← Finset.mul_sum, hsq, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hn (by omega)) (sq_nonneg _)



theorem least_eigenvalue_concave (hn : Module.finrank ℝ E = 3)
    {T U : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hU : U.IsSymmetric)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV : (a • T + b • U).IsSymmetric) :
    a * hT.eigenvalues hn 2 + b * hU.eigenvalues hn 2 ≤ hV.eigenvalues hn 2 := by
  let v := hV.eigenvectorBasis hn 2
  have hv : ‖v‖ = 1 := (hV.eigenvectorBasis hn).orthonormal.1 2
  have heq : inner ℝ v ((a • T + b • U) v) = hV.eigenvalues hn 2 := by
    rw [hV.apply_eigenvectorBasis hn 2, inner_smul_right]
    change hV.eigenvalues hn 2 * inner ℝ v v = hV.eigenvalues hn 2
    simp [hv]
  rw [← heq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_right, inner_smul_right]
  exact add_le_add (mul_le_mul_of_nonneg_left (rayleigh_ge_least hT hn hv) ha)
    (mul_le_mul_of_nonneg_left (rayleigh_ge_least hU hn hv) hb)

theorem negative_least_eigenvalue_convex (hn : Module.finrank ℝ E = 3)
    {T U : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hU : U.IsSymmetric)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV : (a • T + b • U).IsSymmetric) :
    max (-(hV.eigenvalues hn 2)) 0 ≤
      a * max (-(hT.eigenvalues hn 2)) 0 + b * max (-(hU.eigenvalues hn 2)) 0 := by
  have heig := least_eigenvalue_concave hn hT hU ha hb hV
  apply max_le
  · have hT' := mul_le_mul_of_nonneg_left (le_max_left (-(hT.eigenvalues hn 2)) 0) ha
    have hU' := mul_le_mul_of_nonneg_left (le_max_left (-(hU.eigenvalues hn 2)) 0) hb
    linarith
  · exact add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hb (le_max_right _ _))

def region {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = 3) (t : ℝ) :
    Set (E →ₗ[ℝ] E) :=
  {T | ∃ hT : T.IsSymmetric,
    (LinearMap.trace ℝ E T, max (-(hT.eigenvalues hn 2)) 0) ∈ scalarRegion t}

theorem convex_region {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) : Convex ℝ (region hn t) := by
  intro T hT U hU a b ha hb hab
  obtain ⟨hT, hTmem⟩ := hT
  obtain ⟨hU, hUmem⟩ := hU
  have hV : (a • T + b • U).IsSymmetric :=
    (hT.smul (by simp)).add (hU.smul (by simp))
  refine ⟨hV, ?_⟩
  have hscalar := convex_scalarRegion ht hTmem hUmem ha hb hab
  have htrace : LinearMap.trace ℝ E (a • T + b • U) =
      a * LinearMap.trace ℝ E T + b * LinearMap.trace ℝ E U := by
    simp
  rw [htrace]
  exact scalarRegion_downward ht hscalar (negative_least_eigenvalue_convex hn hT hU ha hb hV)

end Poincare.HamiltonIvey
