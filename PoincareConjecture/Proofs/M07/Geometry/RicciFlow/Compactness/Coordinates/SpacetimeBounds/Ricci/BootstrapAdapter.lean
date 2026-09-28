import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Equation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Prolongation



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SpacetimeBounds

open Bootstrap

def twoJetProjection (n : ℕ) :
    Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2 →L[ℝ] MetricTwoJet n :=
  let E := EuclideanSpace ℝ (Fin n)
  let V := MetricCoefficient n
  ((continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj 0)).prod
      (((continuousMultilinearCurryFin1 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.proj 1)).prod
        (((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] V)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (continuousMultilinearCurryRightEquiv' ℝ 1 E V).toContinuousLinearEquiv.toContinuousLinearMap).comp
            (ContinuousLinearMap.proj 2)))

theorem twoJetProjection_spatialJet {n : ℕ}
    (f : ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    twoJetProjection n (spatialJet 2 f z) = metricTwoJet (fun x => f (z.1, x)) z.2 := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ext u v w
      simp only [twoJetProjection, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, continuousMultilinearCurryFin1_apply, metricTwoJet]
      change iteratedFDeriv ℝ 1 (fun x => f (z.1, x)) z.2 (Fin.snoc 0 u) v w = _
      rw [iteratedFDeriv_one_apply]
      simp
    · ext u v w y
      simp [twoJetProjection, metricTwoJet]
      change iteratedFDeriv ℝ 2 (fun x => f (z.1, x)) z.2 ![u, v] w y = _
      rw [iteratedFDeriv_two_apply]
      rfl

def jetRicciFlowOperator (n : ℕ) := ricciFlowOperator n ∘ twoJetProjection n

def jetRicciFlowDomain (n : ℕ) : Set (Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2) :=
  (twoJetProjection n) ⁻¹' {J : MetricTwoJet n | J.1.IsInvertible}

theorem isOpen_jetRicciFlowDomain (n : ℕ) : IsOpen (jetRicciFlowDomain n) :=
  (isOpen_ricciFlowOperator_domain n).preimage (twoJetProjection n).continuous

theorem contDiffOn_jetRicciFlowOperator (n : ℕ) :
    ContDiffOn ℝ ∞ (jetRicciFlowOperator n) (jetRicciFlowDomain n) :=
  (contDiffOn_ricciFlowOperator n).comp (twoJetProjection n).contDiff.contDiffOn (fun _ h => h)

theorem baseProjection_zero {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (n r : ℕ) (a : Jet E V (n + r)) :
    baseProjection n r a 0 = a 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change baseProjection n r (truncate (n + r) a) 0 = a 0
      rw [ih]
      rfl



theorem exists_compact_elliptic_jet_box (n r : ℕ) {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∃ K : Set (Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) (2 + r)),
      IsCompact K ∧ K ⊆ (baseProjection 2 r) ⁻¹' jetRicciFlowDomain n ∧
      ∀ J, ‖J‖ ≤ B →
        (∀ v, a * ‖v‖ ^ 2 ≤
          (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n))
            (MetricCoefficient n) (J 0)) v v) → J ∈ K := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := MetricCoefficient n
  have hfd (j : ℕ) : FiniteDimensional ℝ (E [×j]→L[ℝ] V) := by
    induction j with
    | zero =>
        exact FiniteDimensional.of_injective (continuousMultilinearCurryFin0 ℝ E V).toLinearMap
          (continuousMultilinearCurryFin0 ℝ E V).injective
    | succ j ih =>
        let := ih
        exact FiniteDimensional.of_injective
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V).toLinearMap
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V).injective
  let : ∀ j : Fin (2 + r + 1), FiniteDimensional ℝ (E [×(j : ℕ)]→L[ℝ] V) :=
    fun j => hfd j
  let : ProperSpace (Jet E V (2 + r)) := FiniteDimensional.proper ℝ _
  let ev : Jet E V (2 + r) →L[ℝ] V :=
    (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.proj 0)
  let K := {J : Jet E V (2 + r) | ‖J‖ ≤ B ∧ ∀ v, a * ‖v‖ ^ 2 ≤ ev J v v}
  have hclosed : IsClosed K := by
    apply (isClosed_le continuous_norm continuous_const).inter
    change IsClosed {J : Jet E V (2 + r) | ∀ v, a * ‖v‖ ^ 2 ≤ ev J v v}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const
      ((ev.continuous.clm_apply continuous_const).clm_apply continuous_const)
  have hcompact : IsCompact K :=
    (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hclosed,
      isBounded_iff_forall_norm_le.mpr ⟨B, fun _ h => h.1⟩⟩
  refine ⟨K, hcompact, ?_, fun J hnorm hell => ⟨hnorm, hell⟩⟩
  intro J hJ
  change ((twoJetProjection n (baseProjection 2 r J)).1).IsInvertible
  apply CoordinateTransition.isInvertible_of_uniformEllipticity ha
  intro v
  change a * ‖v‖ ^ 2 ≤ (continuousMultilinearCurryFin0 ℝ E V
    (baseProjection 2 r J 0)) v v
  rw [baseProjection_zero]
  exact hJ.2 v

end PoincareConjecture.SpacetimeBounds
