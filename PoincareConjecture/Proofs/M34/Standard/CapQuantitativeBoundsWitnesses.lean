import PoincareConjecture.Proofs.M34.Standard.CapQuantitativeBounds
import PoincareConjecture.Proofs.M34.Standard.CapQuantitativeBoundsConstants
import PoincareConjecture.Proofs.M34.Standard.CapQuantitativeBoundsGeometry










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

variable {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
  {h : RiemannianMetric 3 X}



theorem scalarCurvatureSupOn_bounds_of_interval (D : LeviCivitaData h)
    {V : Set X} (hne : V.Nonempty) {a b : ℝ}
    (hb : ∀ x ∈ V, a ≤ D.scalarCurvature x ∧ D.scalarCurvature x ≤ b) :
    a ≤ scalarCurvatureSupOn h D V ∧ scalarCurvatureSupOn h D V ≤ b := by
  obtain ⟨x, hx⟩ := hne
  have hbounded : BddAbove (range (fun z : V => D.scalarCurvature z.1)) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (hb z.1 z.2).2
  refine ⟨(hb x hx).1.trans (le_csSup hbounded ⟨⟨x, hx⟩, rfl⟩), ?_⟩
  exact csSup_le ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩ (by
    rintro _ ⟨z, rfl⟩
    exact (hb z.1 z.2).2)

end PoincareConjecture

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [MeasurableSpace X] [BorelSpace X] [T3Space X]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)




theorem image_recut_quantitative_bounds
    {C K : ℝ} (hC1 : 1 ≤ C) (hC : N.cap_constant ≤ C)
    (hK : M34.capPersistenceUpperConstant C < K)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (e : OpenPartialHomeomorph M X) {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹)
    (hsource : N.recutCarrier b ⊆ e.source)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hbound : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 2 * g.tangentNorm x v)
    (hscalar : ∀ x ∈ N.recutCarrier b,
      |D.scalarCurvature (e x) - N.connection.scalarCurvature x| ≤ (2 * C)⁻¹)
    (hgradient : ∀ x ∈ N.recutCarrier b,
      |scalarGradientNorm h D (e x) - scalarGradientNorm g N.connection x| ≤ 1)
    (hevolution : ∀ x ∈ N.recutCarrier b,
      |(D.laplacian D.scalarCurvature (e x) + 2 * D.ricciNormSq (e x)) -
        (N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x)| ≤ 1) :
    let V := e '' N.recutCarrier b
    (∀ x ∈ V, 0 < D.scalarCurvature x) ∧
    intrinsicDiameter h V < ENNReal.ofReal
      (K * scalarCurvatureSupOn h D V ^ (-1 / 2 : ℝ)) ∧
    (∃ bound : ℝ, bound < K ∧ ∀ x ∈ V, ∀ y ∈ V,
      D.scalarCurvature y ≤ bound * D.scalarCurvature x) ∧
    calibratedMetricVolume h V < ENNReal.ofReal K *
      ENNReal.ofReal (scalarCurvatureSupOn h D V ^ (-3 / 2 : ℝ)) ∧
    (∃ bound : ℝ, bound < K ∧ ∀ x ∈ V,
      scalarGradientNorm h D x ≤ bound * D.scalarCurvature x ^ (3 / 2 : ℝ)) ∧
    (∃ bound : ℝ, bound < K ∧ ∀ x ∈ V,
      |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤
        bound * D.scalarCurvature x ^ 2) := by
  let V := e '' N.recutCarrier b
  let S := scalarCurvatureSupOn h D V
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hKpos := (M34.capPersistenceUpperConstant_pos hCpos.le).trans hK
  have hupper := M34.capPersistenceUpperConstant_witnesses hCpos.le
  have hvalues := N.scalar_bounds_on_image_of_close hC1 hC ho hnormal D e
    (N.recutCarrier_subset_carrier b) hscalar
  have hne : V.Nonempty := by
    obtain ⟨x, hx⟩ := N.core_nonempty
    have hxY : x ∈ N.closed_core := interior_subset (N.core_eq_interior_closed_core ▸ hx)
    exact ⟨e x, ⟨x, Or.inl hxY, rfl⟩⟩
  have hS := scalarCurvatureSupOn_bounds_of_interval D hne hvalues
  have hSpos : 0 < S := (inv_pos.mpr (by positivity : 0 < 2 * C)).trans_le hS.1
  have hpower (p : ℝ) (hp : 0 ≤ p) : 1 ≤ (2 * C) ^ p * S ^ (-p) := by
    rw [Real.rpow_neg hSpos.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hSpos p)).mpr
    simpa only [one_mul] using Real.rpow_le_rpow hSpos.le hS.2 hp
  have hdiamCoeff : 4 * C ≤ K * S ^ (-1 / 2 : ℝ) := by
    calc
      _ ≤ (4 * C) * ((2 * C) ^ (1 / 2 : ℝ) * S ^ (-(1 / 2 : ℝ))) :=
        le_mul_of_one_le_right (by positivity) (hpower _ (by norm_num))
      _ = (4 * C * (2 * C) ^ (1 / 2 : ℝ)) * S ^ (-1 / 2 : ℝ) := by ring
      _ ≤ K * S ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hupper.2.1.trans hK).le (Real.rpow_nonneg hSpos.le _)
  have hvolCoeff : 8 * C ≤ K * S ^ (-3 / 2 : ℝ) := by
    calc
      _ ≤ (8 * C) * ((2 * C) ^ (3 / 2 : ℝ) * S ^ (-(3 / 2 : ℝ))) :=
        le_mul_of_one_le_right (by positivity) (hpower _ (by norm_num))
      _ = (8 * C * (2 * C) ^ (3 / 2 : ℝ)) * S ^ (-3 / 2 : ℝ) := by ring
      _ ≤ K * S ^ (-3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hupper.2.2.1.trans hK).le (Real.rpow_nonneg hSpos.le _)
  refine ⟨fun x hx => (inv_pos.mpr (by positivity : 0 < 2 * C)).trans_le (hvalues x hx).1,
    ?_, ⟨(2 * C) ^ 2, hupper.1.trans hK, ?_⟩, ?_,
    ⟨_, hupper.2.2.2.1.trans hK, ?_⟩, ⟨_, hupper.2.2.2.2.trans hK, ?_⟩⟩
  · exact (N.image_recut_intrinsicDiameter_lt hC ho hnormal h e hb hb'
      (hf.mono hsource) (fun x hx => hbound x (hsource hx))).trans_le
      (ENNReal.ofReal_le_ofReal hdiamCoeff)
  · intro x hx y hy
    have hm : 1 ≤ 2 * C * D.scalarCurvature x :=
      (inv_le_iff_one_le_mul₀' (by positivity : 0 < 2 * C)).mp (hvalues x hx).1
    calc
      _ ≤ 2 * C := (hvalues y hy).2
      _ ≤ (2 * C) * (2 * C * D.scalarCurvature x) :=
        le_mul_of_one_le_right (by positivity) hm
      _ = _ := by ring
  · rw [← ENNReal.ofReal_mul hKpos.le]
    exact (N.image_recut_volume_lt hC ho hnormal h e hb hb' hsource hf hbound).trans_le
      (ENNReal.ofReal_le_ofReal hvolCoeff)
  · exact N.gradient_bound_on_image_of_close hC1 hC ho hnormal D e
      (N.recutCarrier_subset_carrier b) (fun x hx => (hvalues x hx).1) hgradient
  · exact N.evolution_bound_on_image_of_close hC1 hC ho hnormal D e
      (N.recutCarrier_subset_carrier b) (fun x hx => (hvalues x hx).1) hevolution

end PoincareConjecture.CapCertificate
