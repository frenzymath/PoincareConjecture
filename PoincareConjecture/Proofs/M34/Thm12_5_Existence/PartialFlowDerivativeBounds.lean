import PoincareConjecture.Proofs.M34.Standard.CompleteDerivativeBounds
import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem standardInitial_derivative_bounds_upto {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ x : StandardCapSpace,
      g0.connection.curvatureDerivativeNorm j x ≤ C := by
  induction k with
  | zero =>
      obtain ⟨C, hC, hb⟩ := E0.curvature_derivative_bounds 0
      refine ⟨C, hC, fun j hj x => ?_⟩
      have : j = 0 := by omega
      subst j
      exact hb x
  | succ k ih =>
      obtain ⟨C, hC, hb⟩ := ih
      obtain ⟨A, _hA, ha⟩ := E0.curvature_derivative_bounds (k + 1)
      refine ⟨max C A, hC.trans (le_max_left _ _), fun j hj x => ?_⟩
      by_cases hjk : j ≤ k
      · exact (hb j hjk x).trans (le_max_left _ _)
      · have : j = k + 1 := by omega
        subst j
        exact (ha x).trans (le_max_right _ _)

theorem partialFlow_curvatureDerivative_bound (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨A, _hA, hA⟩ := standardInitial_derivative_bounds_upto E0 k
  obtain ⟨C, hC, hest⟩ := complete_initial_derivative_bound P 3 k
    (hB.trans_le (le_max_left B A)) hS
  have hpair : (⟨F.flow.metric 0, F.flow.connection 0⟩ :
      Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g) =
        ⟨g0.metric, g0.connection⟩ :=
    Sigma.mk.inj_iff.mpr ⟨F.initial_metric, F.initial_connection⟩
  have hinit (j : ℕ) (hj : j ≤ k) (x : StandardCapSpace) :
      (F.flow.connection 0).curvatureDerivativeNorm j x ≤ A := by
    have heq := congrArg (fun p : Σ g : RiemannianMetric 3 StandardCapSpace,
      LeviCivitaData g => p.2.curvatureDerivativeNorm j x) hpair
    exact heq.le.trans (hA j hj x)
  refine ⟨C, hC, fun t ht x => ?_⟩
  let T := (t + S) / 2
  have hT : 0 < T := by dsimp [T]; linarith [ht.1]
  have htT : t ≤ T := by dsimp [T]; linarith [ht.2]
  have hTS : T < S := by dsimp [T]; linarith [ht.2]
  have hsub : Icc 0 T ⊆ Ico 0 F.lifetime :=
    fun _ hs => ⟨hs.1, hs.2.trans_lt (hTS.trans_le hSF)⟩
  have hne : (Icc 0 T).Nontrivial :=
    ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, ne_of_lt hT⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F.flow hsub ordConnected_Icc hne
  apply hest StandardCapSpace T hT hTS.le G
  · change MetricComplete (F.flow.metric 0)
    rw [F.initial_metric]
    exact g0.complete
  · exact fun s hs y => (hfull s ⟨hs.1, hs.2.trans_lt hTS⟩ y).trans (le_max_left _ _)
  · exact fun j hj y => (hinit j hj y).trans (le_max_right _ _)
  · exact ⟨ht.1, htT⟩

end PoincareConjecture.M34
