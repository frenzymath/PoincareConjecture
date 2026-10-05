import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.AbsoluteRestart
import PoincareLib.Geometry.RicciFlow.Pinching.Conclusion
import PoincareLib.Geometry.Riemannian.Connection.Uniqueness

/-!
# Pinching along the maximal ordinary restart

Each time of the maximal restart lies in a finite ordinary interval. Restricting
to that interval applies the unchanged absolute-time Hamilton--Ivey service.
Reference: Morgan--Tian, Theorem 4.32, pp. 79-80, and Lemma 15.11, pp. 364-365.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.Surgery.OrdinaryRestart

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g₀ : RiemannianMetric 3 M}

/-- The absolute-time pinching predicate depends only on the metric. -/
theorem pinchedAt_iff_of_metric_eq {g h : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (t : ℝ) :
    HamiltonIveyPinchedAt D t ↔ HamiltonIveyPinchedAt D' t := by
  subst h
  have hneg (x : M) : D.negativeCurvaturePart x = D'.negativeCurvaturePart x := by
    simp only [LeviCivitaData.negativeCurvaturePart, LeviCivitaData.leastSectionalCurvature,
      D.curvatureTensor_eq D']
  simp only [HamiltonIveyPinchedAt, D.scalarCurvature_eq D', hneg]

/-- Pinching of the terminal metric supplies the initial pinching hypothesis
for the selected ordinary restart connection. -/
theorem absoluteFlow_initial_pinched
    (hunique : RicciFlowUniqueness 3 M) (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a)
    (D₀ : LeviCivitaData g₀) (hpinched : HamiltonIveyPinchedAt D₀ a) :
    HamiltonIveyPinchedAt (absoluteFlow hunique A a ha |>.connection a) a := by
  exact (pinchedAt_iff_of_metric_eq _ D₀ (absoluteFlow_initial hunique A a ha) a).mpr hpinched

/-- Every time of the maximal restart is contained in a finite interval
starting at the surgery time. -/
theorem exists_finite_absolute_interval (a : ℝ) (ha : 0 ≤ a) {t : ℝ}
    (ht : a ≤ t ∧ ENNReal.ofReal t < ENNReal.ofReal a + lifetime g₀) :
    ∃ b : ℝ, t < b ∧
      Ico a b ⊆ {s : ℝ | a ≤ s ∧ ENNReal.ofReal s < ENNReal.ofReal a + lifetime g₀} := by
  obtain ⟨B, hB⟩ := exists_solution_at (sub_nonneg.mpr ht.1)
    ((absolute_time_lt ha ht.1).mpr ht.2)
  refine ⟨a + B.time, by linarith, ?_⟩
  intro s hs
  exact ⟨hs.1, (absolute_time_lt ha hs.1).mp (solution_time_lt B (by linarith [hs.2]))⟩

/-- The finite-interval pinching service gives pinching on the whole maximal
restart, with its absolute clock unchanged. -/
theorem absoluteFlow_pinched
    (hunique : RicciFlowUniqueness 3 M) (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a)
    (hpinching : ∀ b : ℝ, a < b → ∀ F : RicciFlow 3 M (Ico a b),
      HamiltonIveyPinchedAt (F.connection a) a → HamiltonIveyPinchingConclusion a b F)
    (hinitial : HamiltonIveyPinchedAt (absoluteFlow hunique A a ha |>.connection a) a) :
    ∀ t ∈ {s : ℝ | a ≤ s ∧ ENNReal.ofReal s < ENNReal.ofReal a + lifetime g₀},
      HamiltonIveyPinchedAt (absoluteFlow hunique A a ha |>.connection t) t := by
  intro t ht
  obtain ⟨b, htb, hsub⟩ := exists_finite_absolute_interval a ha ht
  have hab : a < b := ht.1.trans_lt htb
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    (absoluteFlow hunique A a ha) hsub ordConnected_Ico
    ⟨a, ⟨le_rfl, hab⟩, (a + b) / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  exact (hpinching b hab F hinitial).persistence t ⟨ht.1, htb⟩

/-- The full-curvature estimate also passes to each maximal-restart time. -/
theorem absoluteFlow_full_norm_bound
    (hunique : RicciFlowUniqueness 3 M) (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a)
    (hpinching : ∀ b : ℝ, a < b → ∀ F : RicciFlow 3 M (Ico a b),
      HamiltonIveyPinchedAt (F.connection a) a → HamiltonIveyPinchingConclusion a b F)
    (hinitial : HamiltonIveyPinchedAt (absoluteFlow hunique A a ha |>.connection a) a)
    (R₀ t : ℝ)
    (ht : a ≤ t ∧ ENNReal.ofReal t < ENNReal.ofReal a + lifetime g₀) (x : M)
    (hR : (absoluteFlow hunique A a ha |>.connection t).scalarCurvature x ≤ R₀) :
    (absoluteFlow hunique A a ha |>.connection t).curvatureTensorNorm x ≤
      13 * max R₀ (Real.exp 4) := by
  obtain ⟨b, htb, hsub⟩ := exists_finite_absolute_interval a ha ht
  have hab : a < b := ht.1.trans_lt htb
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    (absoluteFlow hunique A a ha) hsub ordConnected_Ico
    ⟨a, ⟨le_rfl, hab⟩, (a + b) / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  exact (hpinching b hab F hinitial).full_norm_bound R₀ t ⟨ht.1, htb⟩ x hR

end PoincareMT.Surgery.OrdinaryRestart
