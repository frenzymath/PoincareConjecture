import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientMaximum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientHomothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciSpectrum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Einstein
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciPositive











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [CompactSpace M]
  {S : GradientShrinkingSolitonData 3 M}

theorem ricciNormSq_eq_scalarSq_div_three_of_compact_ricci_pos
    (hC : RicciFlowCurvatureTheory.{u}) (G : ShrinkingSolitonFlow S)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 → 0 < S.connection.ricci x v v)
    {t : ℝ} (ht : t < 0) (y : M) :
    (G.flow.connection t).ricciNormSq y = (G.flow.connection t).scalarCurvature y ^ 2 / 3 := by
  let D := G.flow.connection t
  have hD := hC.tensor_calculus 3 M (G.flow.metric t) D
  have hRS (z : M) : 0 < S.connection.scalarCurvature z :=
    S.connection.scalarCurvature_pos_of_ricci_pos
      (hC.tensor_calculus 3 M S.metric S.connection) z (hRic z)
  have hR (z : M) : 0 < D.scalarCurvature z := G.scalarCurvature_pos_at_time hRS ht z
  have hRicT (z : M) (v : TangentSpace (𝓡 3) z) (hv : v ≠ 0) : 0 < D.ricci z v v := by
    obtain ⟨E⟩ := G.self_similar t ht
    exact E.ricci_pos (abs_pos.mpr ht.ne) S.connection D hRic z v hv
  obtain ⟨x, hmax, htime⟩ := G.exists_stationary_normalizedRicciNormSq_max hC hRS ht
  have hlocal : IsLocalMax (fun z => D.ricciNormSq z / D.scalarCurvature z ^ 2) x :=
    Filter.Eventually.of_forall (hmax t ht)
  have hineq := G.flow.normalizedRicciNormSq_deriv_le_at_localMax hC
    (show t ∈ interior (Set.Iio 0) by simpa only [interior_Iio, Set.mem_Iio] using ht) hR hlocal
  rw [htime] at hineq
  let b := (G.flow.metric t).orthonormalBasis x
  let Q := ∑ i, ∑ j, D.ricci x (b i) (b j) *
    (∑ a, ∑ c, D.curvatureTensor x (b i) (b a) (b j) (b c) * D.ricci x (b a) (b c))
  have hreact : 0 ≤ D.scalarCurvature x * Q - D.ricciNormSq x ^ 2 := by
    change 0 ≤ 4 * (Q - D.ricciNormSq x ^ 2 / D.scalarCurvature x) /
      D.scalarCurvature x ^ 2 at hineq
    have hnum := (le_div_iff₀ (sq_pos_of_pos (hR x))).mp hineq
    rw [zero_mul] at hnum
    have hQ := (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)).mp hnum
    have hmul := (div_le_iff₀ (hR x)).mp (sub_nonneg.mp hQ)
    nlinarith only [hmul]
  have hx := D.ricciNormSq_eq_scalarSq_div_three_of_reaction_nonneg hD x (hRicT x) hreact
  have hqy := hmax t ht y
  change D.ricciNormSq y / D.scalarCurvature y ^ 2 ≤
    D.ricciNormSq x / D.scalarCurvature x ^ 2 at hqy
  rw [hx] at hqy
  have hqx : (D.scalarCurvature x ^ 2 / 3) / D.scalarCurvature x ^ 2 = (1 / 3 : ℝ) := by
    field_simp [(hR x).ne']
  rw [hqx] at hqy
  apply le_antisymm
  · have hu := (div_le_iff₀ (sq_pos_of_pos (hR y))).mp hqy
    linarith only [hu]
  · exact D.scalarSq_div_three_le_ricciNormSq_of_ricci_pos hD y (hRicT y)

theorem einstein_at_time_of_compact_ricci_pos
    (hC : RicciFlowCurvatureTheory.{u}) (G : ShrinkingSolitonFlow S)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 → 0 < S.connection.ricci x v v)
    {t : ℝ} (ht : t < 0) (x : M) (u v : TangentSpace (𝓡 3) x) :
    (G.flow.connection t).ricci x u v = ((G.flow.connection t).scalarCurvature x / 3) *
      (G.flow.metric t).inner x u v :=
  (G.flow.connection t).ricci_eq_scalar_div_three_mul_inner_of_norm_eq x
    (G.ricciNormSq_eq_scalarSq_div_three_of_compact_ricci_pos hC hRic ht x) u v



theorem compactRoundModel_of_ricci_pos
    (hC : RicciFlowCurvatureTheory.{u}) (G : ShrinkingSolitonFlow S)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 → 0 < S.connection.ricci x v v) :
    Nonempty (CompactRoundShrinkingModel G) := by
  refine ⟨⟨inferInstance, fun t ht => ?_⟩⟩
  apply (G.flow.connection t).constantPositiveSectionalCurvature_of_three_dimensional_einstein
    (hC.tensor_calculus 3 M (G.flow.metric t) (G.flow.connection t))
    (G.einstein_at_time_of_compact_ricci_pos hC hRic ht)
  apply G.scalarCurvature_pos_at_time _ ht
  intro x
  exact S.connection.scalarCurvature_pos_of_ricci_pos
    (hC.tensor_calculus 3 M S.metric S.connection) x (hRic x)



theorem compactRoundModel
    (hC : RicciFlowCurvatureTheory.{u}) (G : ShrinkingSolitonFlow S) :
    Nonempty (CompactRoundShrinkingModel G) :=
  G.compactRoundModel_of_ricci_pos hC (G.ricci_pos_of_compact hC)

end PoincareConjecture.ShrinkingSolitonFlow
