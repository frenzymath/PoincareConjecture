import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.AbsoluteRestart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Conclusion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Surgery.OrdinaryRestart

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g₀ : RiemannianMetric 3 M}


theorem pinchedAt_iff_of_metric_eq {g h : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (t : ℝ) :
    HamiltonIveyPinchedAt D t ↔ HamiltonIveyPinchedAt D' t := by
  subst h
  have hneg (x : M) : D.negativeCurvaturePart x = D'.negativeCurvaturePart x := by
    simp only [LeviCivitaData.negativeCurvaturePart, LeviCivitaData.leastSectionalCurvature,
      D.horizon_curvatureTensor_eq D']
  simp only [HamiltonIveyPinchedAt, D.scalarCurvature_eq D', hneg]



theorem absoluteFlow_initial_pinched
    (hunique : RicciFlowUniqueness 3 M) (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a)
    (D₀ : LeviCivitaData g₀) (hpinched : HamiltonIveyPinchedAt D₀ a) :
    HamiltonIveyPinchedAt (absoluteFlow hunique A a ha |>.connection a) a := by
  exact (pinchedAt_iff_of_metric_eq _ D₀ (absoluteFlow_initial hunique A a ha) a).mpr hpinched



theorem exists_finite_absolute_interval (a : ℝ) (ha : 0 ≤ a) {t : ℝ}
    (ht : a ≤ t ∧ ENNReal.ofReal t < ENNReal.ofReal a + lifetime g₀) :
    ∃ b : ℝ, t < b ∧
      Ico a b ⊆ {s : ℝ | a ≤ s ∧ ENNReal.ofReal s < ENNReal.ofReal a + lifetime g₀} := by
  obtain ⟨B, hB⟩ := exists_solution_at (sub_nonneg.mpr ht.1)
    ((absolute_time_lt ha ht.1).mpr ht.2)
  refine ⟨a + B.time, by linarith, ?_⟩
  intro s hs
  exact ⟨hs.1, (absolute_time_lt ha hs.1).mp (solution_time_lt B (by linarith [hs.2]))⟩



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

end PoincareConjecture.Surgery.OrdinaryRestart
