import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_FiniteScalarBound
import PoincareConjecture.Proofs.M36.ComparisonCovariantJets
import PoincareConjecture.Proofs.M36.ComparisonCoordinateJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance curvatureCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance curvatureCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance curvatureTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance curvatureTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem exists_curvature_component_jet_bound (m : ℕ) {a : ℝ} (ha : 0 < a) (Z : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : RiemannianMetric 3 E) (D : LeviCivitaData g) (x : E),
      (∀ v : E, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
      (∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ Z) →
      ∀ j ≤ m, ∀ b : Fin 4 → Fin 3,
        ‖iteratedFDeriv ℝ j (comparisonTensorComponent D.riemannEvaluation b) x‖ ≤ C := by
  classical
  let : FiniteDimensional ℝ (MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (E →L[ℝ] MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (MetricTwoJet 3) := by infer_instance
  let : ProperSpace (MetricTwoJet 3) := FiniteDimensional.proper ℝ (MetricTwoJet 3)
  let K : Set (MetricTwoJet 3) := {J | ‖J‖ ≤ Z ∧ ∀ v : E, a * ‖v‖ ^ 2 ≤ J.1 v v}
  have hK : IsCompact K := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    constructor
    · apply (isClosed_le continuous_norm continuous_const).inter
      change IsClosed {J : MetricTwoJet 3 | ∀ v : E, a * ‖v‖ ^ 2 ≤ J.1 v v}
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro v
      exact isClosed_le continuous_const
        ((continuous_fst.clm_apply continuous_const).clm_apply continuous_const)
    · exact isBounded_iff_forall_norm_le.mpr ⟨Z, fun _ hJ => hJ.1⟩
  let f (b : Fin 4 → Fin 3) (J : MetricTwoJet 3) : ℝ :=
    jetCurvature J (e (b 0)) (e (b 1)) (e (b 2)) (e (b 3))
  have hf (b : Fin 4 → Fin 3) (J : MetricTwoJet 3) (hJ : J ∈ K) :
      ContDiffAt ℝ ∞ (f b) J :=
    contDiffAt_jetCurvature (CoordinateTransition.isInvertible_of_uniformEllipticity ha hJ.2)
      _ _ _ _
  choose A hA hAbound using fun b : Fin 4 → Fin 3 =>
    exists_compact_local_jet_bound hK (hf b) m
  let A0 := 1 + ∑ b : Fin 4 → Fin 3, A b
  have hA0 : 0 ≤ A0 := by
    apply add_nonneg zero_le_one
    exact Finset.sum_nonneg (fun b _ => zero_le_one.trans (hA b))
  have hAA (b : Fin 4 → Fin 3) : A b ≤ A0 := by
    have h := Finset.single_le_sum (fun c _ => zero_le_one.trans (hA c))
      (Finset.mem_univ b)
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  let B := max Z 1
  have hB : 1 ≤ B := le_max_right _ _
  refine ⟨(m.factorial : ℝ) * A0 * B ^ m, by positivity, ?_⟩
  intro g D x hell hjets j hj b
  have hg := g.contDiffAt_euclideanCoefficients x
  have hjet : ContDiffAt ℝ ∞ (metricTwoJet g.euclideanCoefficients) x :=
    contDiffAt_metricTwoJet hg
  have hJ : metricTwoJet g.euclideanCoefficients x ∈ K := by
    refine ⟨?_, hell⟩
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_metricTwoJet_le (m := 0) hg (fun l hl => hjets l (by omega))
  have hjetbound (l : ℕ) (hl : l ≤ m) :
      ‖iteratedFDeriv ℝ l (metricTwoJet g.euclideanCoefficients) x‖ ≤ B :=
    (norm_iteratedFDeriv_metricTwoJet_le hg (fun q hq => hjets q (by omega))).trans
      (le_max_left _ _)
  have heq : comparisonTensorComponent D.riemannEvaluation b =
      f b ∘ metricTwoJet g.euclideanCoefficients := by
    funext y
    exact (jetCurvature_metricTwoJet D y (e (b 0)) (e (b 1)) (e (b 2)) (e (b 3))).symm
  rw [heq]
  apply (norm_iteratedFDeriv_comp_uniform_at hjet (hf b _ hJ) j hB
    (fun l hl => (hAbound b l (hl.trans hj) _ hJ).trans (hAA b))
    (fun l _ hl => hjetbound l (hl.trans hj))).trans
  gcongr

end PoincareConjecture.M44
