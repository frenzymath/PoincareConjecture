import PoincareConjecture.Proofs.M34.Thm12_5_Existence.CompactCurvatureBound
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.FlowUnion
import PoincareConjecture.Statements.Ch04.Continuation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

theorem exists_compactFlow_past_small_time (P : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (D0 : LeviCivitaData g0)
    {B τ : ℝ} (hB : 0 < B) (_hτ : 0 < τ)
    (hsmall : 16 * (n : ℝ) ^ 6 * B * τ ≤ 1 / 2)
    (hinit : ∀ x : M, D0.curvatureTensorNorm x ≤ B) :
    ∃ T : ℝ, τ < T ∧ ∃ F : RicciFlow n M (Ico 0 T), F.metric 0 = g0 := by
  classical
  by_contra hno
  let S : Set ℝ := {T | 0 < T ∧ ∃ F : RicciFlow n M (Ico 0 T), F.metric 0 = g0}
  obtain ⟨T0, hT0, F0, hF0⟩ := P.1 g0
  have hmem0 : T0 ∈ S := ⟨hT0, F0, hF0⟩
  have hSne : S.Nonempty := ⟨T0, hmem0⟩
  have hupper : ∀ T ∈ S, T ≤ τ := by
    intro T hT
    by_contra h
    exact hno ⟨T, lt_of_not_ge h, hT.2⟩
  have hSbdd : BddAbove S := ⟨τ, hupper⟩
  have hstarpos : 0 < sSup S := hT0.trans_le (le_csSup hSbdd hmem0)
  have hstarle : sSup S ≤ τ := csSup_le hSne hupper
  let F : (T : S) → RicciFlow n M (Ico 0 (T : ℝ)) := fun T => T.property.2.choose
  have hFinit (T : S) : (F T).metric 0 = g0 := T.property.2.choose_spec
  have hcompat (T T' : S) : EqOn (F T).metric (F T').metric
      (Ico 0 (T : ℝ) ∩ Ico 0 (T' : ℝ)) := by
    apply P.2.1 _ _ (F T) (F T')
      ⟨⟨le_rfl, T.property.1⟩, fun _ ht => ht.1⟩
      ⟨⟨le_rfl, T'.property.1⟩, fun _ ht => ht.1⟩
    exact (hFinit T).trans (hFinit T').symm
  have hcover : ∀ t ∈ Ico 0 (sSup S), ∃ T : S, t ∈ Ico 0 (T : ℝ) := by
    intro t ht
    obtain ⟨T, hT, htT⟩ := exists_lt_of_lt_csSup hSne ht.2
    exact ⟨⟨T, hT⟩, ht.1, htT⟩
  obtain ⟨G, hG⟩ := exists_forwardFlowUnion (fun T : S => (T : ℝ)) F
    ⟨T0, hmem0⟩ hcompat hstarpos hcover
  have hGinit : G.metric 0 = g0 :=
    (hG ⟨T0, hmem0⟩ ⟨⟨le_rfl, hstarpos⟩, le_rfl, hT0⟩).trans (hFinit _)
  have hGbound0 (x : M) : (G.connection 0).curvatureTensorNorm x ≤ B := by
    rw [curvatureTensorNorm_eq_of_metric_eq hGinit (G.connection 0) D0]
    exact hinit x
  have hGbound : ∀ t ∈ Ico 0 (sSup S), ∀ x : M,
      (G.connection t).curvatureTensorNorm x ≤ 2 * B := by
    intro t ht
    have htτ : t ≤ τ := ht.2.le.trans hstarle
    have hsmallt : 16 * (n : ℝ) ^ 6 * B * t ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left htτ (by positivity)).trans hsmall
    exact compact_curvatureTensorNorm_le_twice G hB hGbound0 ht hsmallt
  obtain ⟨T', hT', G', hG'⟩ := P.2.2 (sSup S) hstarpos G ⟨2 * B, hGbound⟩
  have hnew : T' ∈ S := ⟨hstarpos.trans hT', G',
    (hG' ⟨le_rfl, hstarpos⟩).symm.trans hGinit⟩
  exact (not_lt_of_ge (le_csSup hSbdd hnew)) hT'

theorem exists_compactFlow_on_small_slab (P : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (D0 : LeviCivitaData g0)
    {B τ : ℝ} (hB : 0 < B) (hτ : 0 < τ)
    (hsmall : 16 * (n : ℝ) ^ 6 * B * τ ≤ 1 / 2)
    (hinit : ∀ x : M, D0.curvatureTensorNorm x ≤ B) :
    ∃ F : RicciFlow n M (Icc 0 τ), F.metric 0 = g0 ∧
      ∀ t ∈ Icc 0 τ, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ 2 * B := by
  obtain ⟨T, hT, F, hF⟩ := exists_compactFlow_past_small_time P g0 D0 hB hτ hsmall hinit
  have hsub : Icc 0 τ ⊆ Ico 0 T := fun _ ht => ⟨ht.1, ht.2.trans_lt hT⟩
  have hne : (Icc 0 τ).Nontrivial :=
    ⟨0, ⟨le_rfl, hτ.le⟩, τ, ⟨hτ.le, le_rfl⟩, ne_of_lt hτ⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub ordConnected_Icc hne
  refine ⟨G, hF, ?_⟩
  have hbound0 (x : M) : (F.connection 0).curvatureTensorNorm x ≤ B := by
    rw [curvatureTensorNorm_eq_of_metric_eq hF (F.connection 0) D0]
    exact hinit x
  intro t ht
  have hsmallt : 16 * (n : ℝ) ^ 6 * B * t ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans hsmall
  exact compact_curvatureTensorNorm_le_twice F hB hbound0 (hsub ht) hsmallt

end PoincareConjecture.M34
