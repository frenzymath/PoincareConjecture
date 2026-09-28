import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawRicciCoefficient










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

def rawFirstOrderCoefficient {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (x : V) : (V →L[ℝ] V) →L[ℝ] V :=
  LinearMap.toContinuousLinearMap {
    toFun := fun L => ∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
      (rawConnectionCoefficient D x (e j) (L (e i)) +
        rawConnectionCoefficient D x (e i) (L (e j)) -
        L (rawConnectionCoefficient D x (e i) (e j)))
    map_add' := by
      intro L N
      simp only [add_apply, map_add, smul_add, smul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      module
    map_smul' := by
      intro c L
      simp only [smul_apply, map_smul, smul_add, smul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum, RingHom.id_apply]
      simp only [smul_smul, mul_comm] }

@[simp] theorem rawFirstOrderCoefficient_apply {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x : V) (L : V →L[ℝ] V) :
    rawFirstOrderCoefficient D x L = ∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
      (rawConnectionCoefficient D x (e j) (L (e i)) +
        rawConnectionCoefficient D x (e i) (L (e j)) -
        L (rawConnectionCoefficient D x (e i) (e j))) := rfl

def rawZeroOrderCoefficient {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (x : V) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
      (fderiv ℝ (rawConnectionCoefficient D) x (e i) (e j) z +
        rawConnectionCoefficient D x (e i) (rawConnectionCoefficient D x (e j) z) -
        rawConnectionCoefficient D x (rawConnectionCoefficient D x (e i) (e j)) z)) +
          rawRicciLinear D x z
    map_add' := by
      intro z w
      simp only [map_add, smul_add, smul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      module
    map_smul' := by
      intro c z
      simp only [map_smul, smul_add, smul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.smul_sum, RingHom.id_apply]
      simp only [smul_smul, mul_comm] }

@[simp] theorem rawZeroOrderCoefficient_apply {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x z : V) :
    rawZeroOrderCoefficient D x z =
      (∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
        (fderiv ℝ (rawConnectionCoefficient D) x (e i) (e j) z +
          rawConnectionCoefficient D x (e i) (rawConnectionCoefficient D x (e j) z) -
          rawConnectionCoefficient D x (rawConnectionCoefficient D x (e i) (e j)) z)) +
            rawRicciLinear D x z := rfl

theorem rawFirstOrderCoefficient_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) : ContDiff ℝ ∞ (rawFirstOrderCoefficient D) := by
  apply contDiff_clm_apply_iff.mpr
  intro L
  simp only [rawFirstOrderCoefficient_apply]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  apply (raw_inverseGram_entry_contDiff g i j).smul
  have hC := rawConnectionCoefficient_contDiff D
  exact (((hC.clm_apply contDiff_const).clm_apply contDiff_const).add
    ((hC.clm_apply contDiff_const).clm_apply contDiff_const)).sub
      (L.contDiff.comp ((hC.clm_apply contDiff_const).clm_apply contDiff_const))

theorem rawZeroOrderCoefficient_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) : ContDiff ℝ ∞ (rawZeroOrderCoefficient D) := by
  apply contDiff_clm_apply_iff.mpr
  intro z
  simp only [rawZeroOrderCoefficient_apply]
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    apply (raw_inverseGram_entry_contDiff g i j).smul
    have hC := rawConnectionCoefficient_contDiff D
    have hdC : ContDiff ℝ ∞ (fderiv ℝ (rawConnectionCoefficient D)) :=
      hC.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
    exact ((((hdC.clm_apply contDiff_const).clm_apply contDiff_const).clm_apply
      contDiff_const).add ((hC.clm_apply contDiff_const).clm_apply
        ((hC.clm_apply contDiff_const).clm_apply contDiff_const))).sub
      ((hC.clm_apply ((hC.clm_apply contDiff_const).clm_apply contDiff_const)).clm_apply
        contDiff_const)
  · exact (rawRicciLinear_contDiff D).clm_apply contDiff_const



theorem exists_raw_compact_lower_order_bound {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {K : Set V} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      (∀ L : V →L[ℝ] V, ‖rawFirstOrderCoefficient D x L‖ ≤ C * ‖L‖) ∧
      (∀ z : V, ‖rawZeroOrderCoefficient D x z‖ ≤ C * ‖z‖) := by
  obtain ⟨A, hA, hbA⟩ :=
    (hK.image (rawFirstOrderCoefficient_contDiff D).continuous).isBounded.exists_pos_norm_le
  obtain ⟨B, hB, hbB⟩ :=
    (hK.image (rawZeroOrderCoefficient_contDiff D).continuous).isBounded.exists_pos_norm_le
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  constructor
  · intro L
    exact ((rawFirstOrderCoefficient D x).le_opNorm L).trans
      (mul_le_mul_of_nonneg_right ((hbA _ ⟨x, hx, rfl⟩).trans (le_max_left _ _))
        (norm_nonneg L))
  · intro z
    exact ((rawZeroOrderCoefficient D x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right ((hbB _ ⟨x, hx, rfl⟩).trans (le_max_right _ _))
        (norm_nonneg z))



theorem raw_vector_heat_full_coordinate_operator {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} (hX : ContDiff ℝ ∞ X) (x : V) :
    (∑ a, fieldHessian D X x (g.orthonormalBasis x a) (g.orthonormalBasis x a)) +
        rawRicciLinear D x (X x) =
      (∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
        fderiv ℝ (fderiv ℝ X) x (e i) (e j)) +
          rawFirstOrderCoefficient D x (fderiv ℝ X x) + rawZeroOrderCoefficient D x (X x) := by
  simp only [fieldHessian_eq_rawHessianBilinear D hX]
  rw [vector_bilinear_trace_inverse_gram g x]
  simp only [rawHessianBilinear, LinearMap.mk₂_apply, rawFirstOrderCoefficient_apply,
    rawZeroOrderCoefficient_apply, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  abel

end PoincareConjecture.M35.Uniqueness.Heat
