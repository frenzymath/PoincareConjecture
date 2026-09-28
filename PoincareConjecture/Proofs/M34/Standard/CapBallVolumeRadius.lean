import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem scalar_normalized_radius_sqrt_bounds
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (y : M)
    {r B : ℝ} (hr : 0 < r) (hB : 0 < B)
    (hnormal : scalarCurvatureSupOn g D (g.ball y r) = r⁻¹ ^ 2)
    (hscalar : ∀ x ∈ g.ball y r, B⁻¹ ≤ D.scalarCurvature x ∧
      D.scalarCurvature x ≤ B) :
    (Real.sqrt B)⁻¹ ≤ r ∧ r ≤ Real.sqrt B := by
  have hy : y ∈ g.ball y r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) y y < ENNReal.ofReal r
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hbdd : BddAbove (range (fun z : g.ball y r => D.scalarCurvature z.1)) :=
    ⟨B, by rintro _ ⟨z, rfl⟩; exact (hscalar z.1 z.2).2⟩
  have hsup : B⁻¹ ≤ scalarCurvatureSupOn g D (g.ball y r) ∧
      scalarCurvatureSupOn g D (g.ball y r) ≤ B := by
    constructor
    · exact (hscalar y hy).1.trans (le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩)
    · exact csSup_le ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩ (by
        rintro _ ⟨z, rfl⟩
        exact (hscalar z.1 z.2).2)
  rw [hnormal] at hsup
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hinv : r⁻¹ ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (inv_nonneg.mpr hr.le) hsqrt.le).mp
    simpa only [Real.sq_sqrt hB.le] using hsup.2
  have hrsq : r ^ 2 ≤ B := by
    apply (inv_le_inv₀ hB (sq_pos_of_pos hr)).mp
    simpa only [inv_pow] using hsup.1
  constructor
  · have hi := (inv_le_inv₀ hsqrt (inv_pos.mpr hr)).mpr hinv
    simpa only [inv_inv] using hi
  · apply (sq_le_sq₀ hr.le hsqrt.le).mp
    rwa [Real.sq_sqrt hB.le]



theorem scalar_normalized_radius_bounds
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (y : M)
    {r B : ℝ} (hr : 0 < r) (hB : 1 ≤ B)
    (hnormal : scalarCurvatureSupOn g D (g.ball y r) = r⁻¹ ^ 2)
    (hscalar : ∀ x ∈ g.ball y r, B⁻¹ ≤ D.scalarCurvature x ∧
      D.scalarCurvature x ≤ B) :
    B⁻¹ ≤ r ∧ r ≤ B := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hs := g.scalar_normalized_radius_sqrt_bounds D y hr hBpos hnormal hscalar
  have hsB : Real.sqrt B ≤ B := Real.sqrt_le_self_iff.mpr (Or.inr hB)
  exact ⟨((inv_le_inv₀ hBpos (Real.sqrt_pos.mpr hBpos)).mpr hsB).trans hs.1,
    hs.2.trans hsB⟩

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)



theorem core_radius_sqrt_bounds_of_normalized_base
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {C : ℝ} (hC : N.cap_constant ≤ C) {y : M} (hy : y ∈ N.core) :
    (Real.sqrt C)⁻¹ ≤ N.core_radius y ∧ N.core_radius y ≤ Real.sqrt C := by
  apply g.scalar_normalized_radius_sqrt_bounds N.connection y
    (N.core_radius_pos y hy) (N.cap_constant_pos.trans_le hC) (N.core_radius_eq y hy)
  intro x hx
  exact N.scalar_bounds_of_normalized_base ho hnormal hC
    (N.core_ball_subset y hy (subset_closure hx))



theorem core_radius_bounds_of_normalized_base
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {C : ℝ} (hC : N.cap_constant ≤ C) (hC1 : 1 ≤ C) {y : M} (hy : y ∈ N.core) :
    C⁻¹ ≤ N.core_radius y ∧ N.core_radius y ≤ C := by
  apply g.scalar_normalized_radius_bounds N.connection y
    (N.core_radius_pos y hy) hC1 (N.core_radius_eq y hy)
  intro x hx
  exact N.scalar_bounds_of_normalized_base ho hnormal hC
    (N.core_ball_subset y hy (subset_closure hx))

end PoincareConjecture.CapCertificate
