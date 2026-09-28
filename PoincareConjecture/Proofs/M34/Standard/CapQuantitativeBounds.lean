import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientNorm










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)



theorem scalar_bounds_on_image_of_close
    {C : ℝ} (hC1 : 1 ≤ C) (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {h : RiemannianMetric 3 X} (D : LeviCivitaData h) (f : M → X)
    {U : Set M} (hU : U ⊆ N.carrier)
    (hclose : ∀ x ∈ U,
      |D.scalarCurvature (f x) - N.connection.scalarCurvature x| ≤ (2 * C)⁻¹) :
    ∀ y ∈ f '' U, (2 * C)⁻¹ ≤ D.scalarCurvature y ∧ D.scalarCurvature y ≤ 2 * C := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hi : C⁻¹ = 2 * (2 * C)⁻¹ := by field_simp
  have hinv : (2 * C)⁻¹ ≤ C := by
    have ht : 1 ≤ 2 * C := by linarith
    have hh : (2 * C)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr ht
    exact hh.trans hC1
  rintro y ⟨x, hx, rfl⟩
  have hbounds := N.scalar_bounds_of_normalized_base ho hnormal hC (hU hx)
  have herror := abs_sub_le_iff.mp (hclose x hx)
  constructor <;> linarith



theorem gradient_le_of_normalized_base
    {C : ℝ} (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {x : M} (hx : x ∈ N.carrier) :
    scalarGradientNorm g N.connection x ≤ C * C ^ (3 / 2 : ℝ) := by
  obtain ⟨b, hb, hgradient⟩ := N.gradient_bound
  have hs := N.scalar_bounds_of_normalized_base ho hnormal hC hx
  have hp := Real.rpow_le_rpow (N.scalar_pos x hx).le hs.2 (by norm_num : (0 : ℝ) ≤ 3 / 2)
  calc
    _ ≤ b * N.connection.scalarCurvature x ^ (3 / 2 : ℝ) := hgradient x hx
    _ ≤ C * N.connection.scalarCurvature x ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (hb.le.trans hC) (Real.rpow_nonneg (N.scalar_pos x hx).le _)
    _ ≤ C * C ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hp (N.cap_constant_pos.trans_le hC).le



theorem evolution_le_of_normalized_base
    {C : ℝ} (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {x : M} (hx : x ∈ N.carrier) :
    |N.connection.laplacian N.connection.scalarCurvature x +
      2 * N.connection.ricciNormSq x| ≤ C * C ^ 2 := by
  obtain ⟨b, hb, hevolution⟩ := N.laplacian_bound
  have hs := N.scalar_bounds_of_normalized_base ho hnormal hC hx
  have hCpos := N.cap_constant_pos.trans_le hC
  have hp := (sq_le_sq₀ (N.scalar_pos x hx).le hCpos.le).mpr hs.2
  calc
    _ ≤ b * N.connection.scalarCurvature x ^ 2 := hevolution x hx
    _ ≤ C * N.connection.scalarCurvature x ^ 2 :=
      mul_le_mul_of_nonneg_right (hb.le.trans hC) (sq_nonneg _)
    _ ≤ C * C ^ 2 := mul_le_mul_of_nonneg_left hp hCpos.le



theorem gradient_bound_on_image_of_close
    {C : ℝ} (hC1 : 1 ≤ C) (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {h : RiemannianMetric 3 X} (D : LeviCivitaData h) (f : M → X)
    {U : Set M} (hU : U ⊆ N.carrier)
    (hscalar : ∀ y ∈ f '' U, (2 * C)⁻¹ ≤ D.scalarCurvature y)
    (hclose : ∀ x ∈ U,
      |scalarGradientNorm h D (f x) - scalarGradientNorm g N.connection x| ≤ 1) :
    ∀ y ∈ f '' U, scalarGradientNorm h D y ≤
      ((C * C ^ (3 / 2 : ℝ) + 1) * (2 * C) ^ (3 / 2 : ℝ)) *
        D.scalarCurvature y ^ (3 / 2 : ℝ) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  rintro y ⟨x, hx, rfl⟩
  have hs := hscalar (f x) ⟨x, hx, rfl⟩
  have hspos : 0 < D.scalarCurvature (f x) := (inv_pos.mpr (by positivity)).trans_le hs
  have hm : 1 ≤ 2 * C * D.scalarCurvature (f x) :=
    (inv_le_iff_one_le_mul₀' (by positivity : 0 < 2 * C)).mp hs
  have hp : 1 ≤ (2 * C) ^ (3 / 2 : ℝ) * D.scalarCurvature (f x) ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 2 * C) hspos.le]
    exact Real.one_le_rpow hm (by norm_num)
  have hg := N.gradient_le_of_normalized_base hC ho hnormal (hU hx)
  have he := (abs_sub_le_iff.mp (hclose x hx)).1
  calc
    _ ≤ C * C ^ (3 / 2 : ℝ) + 1 := by linarith
    _ ≤ (C * C ^ (3 / 2 : ℝ) + 1) *
        ((2 * C) ^ (3 / 2 : ℝ) * D.scalarCurvature (f x) ^ (3 / 2 : ℝ)) :=
      le_mul_of_one_le_right (by positivity) hp
    _ = _ := by ring



theorem evolution_bound_on_image_of_close
    {C : ℝ} (hC1 : 1 ≤ C) (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {h : RiemannianMetric 3 X} (D : LeviCivitaData h) (f : M → X)
    {U : Set M} (hU : U ⊆ N.carrier)
    (hscalar : ∀ y ∈ f '' U, (2 * C)⁻¹ ≤ D.scalarCurvature y)
    (hclose : ∀ x ∈ U,
      |(D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) -
        (N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x)| ≤ 1) :
    ∀ y ∈ f '' U, |D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y| ≤
      ((C * C ^ 2 + 1) * (2 * C) ^ 2) * D.scalarCurvature y ^ 2 := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  rintro y ⟨x, hx, rfl⟩
  have hs := hscalar (f x) ⟨x, hx, rfl⟩
  have hm : 1 ≤ 2 * C * D.scalarCurvature (f x) :=
    (inv_le_iff_one_le_mul₀' (by positivity : 0 < 2 * C)).mp hs
  have hp : 1 ≤ (2 * C) ^ 2 * D.scalarCurvature (f x) ^ 2 := by
    rw [← mul_pow]
    nlinarith
  have hold := N.evolution_le_of_normalized_base hC ho hnormal (hU hx)
  have he0 := abs_le.mp (hclose x hx)
  have hold0 := abs_le.mp hold
  have he : |D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)| ≤
      C * C ^ 2 + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ C * C ^ 2 + 1 := by linarith
    _ ≤ (C * C ^ 2 + 1) * ((2 * C) ^ 2 * D.scalarCurvature (f x) ^ 2) :=
      le_mul_of_one_le_right (by positivity) hp
    _ = _ := by ring

end PoincareConjecture.CapCertificate
