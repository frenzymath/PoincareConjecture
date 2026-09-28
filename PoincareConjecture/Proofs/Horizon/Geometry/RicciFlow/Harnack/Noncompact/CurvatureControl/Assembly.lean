import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Continuation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeToCurvature









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

open Poincare.RicciFlow.Harnack



theorem differentialHarnackAncientTheory_of_component_local_right_curvature_bounds
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hright :
      ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ T₀ T₁ : ℝ, T₀ < T₁ →
        ∀ F : RicciFlow n M (Ioo T₀ T₁),
        (∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t)) →
        (∀ t ∈ Ioo T₀ T₁, ∀ x : M,
          LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
        (∀ t ∈ Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
          ∀ x : M, LeviCivitaData.CurvatureOperatorBound
            (F.connection t) K x) →
        ∀ p : M, ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo T₀ T₁ →
          ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
            ∀ t ∈ Icc c d, ∀ x ∈ connectedComponent p,
              (F.connection t).curvatureTensorNorm x ≤ K) :
    HarnackAncientTheory.{u} := by
  apply Poincare.Geometry.RicciFlow.Harnack.assemble_harnack_from_finite_differential
    hM04
  intro n M _ _ _ _ _ _ T₀ T₁ hT F hcomplete hcurv hbound
  apply finite_differential_of_component_local_right_curvature_bounds
    hM04 F hcomplete hcurv hbound
  intro p a b hab hJ
  exact hright n M T₀ T₁ hT F hcomplete hcurv hbound p a b hab hJ




theorem differentialHarnackAncientTheory_of_bounded_ancient_zero_volume
    (hM04 : RicciFlowCurvatureTheory.{u}) : HarnackAncientTheory.{u} := by
  apply differentialHarnackAncientTheory_of_component_local_right_curvature_bounds hM04
  intro n M _ _ _ _ _ _ T₀ T₁ _ F hcomplete hcurv hbound p a b hab hJ c hc
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1
  obtain ⟨K, hK, hb⟩ := hbound c (hJ ⟨hc.1, hc.2.le⟩)
  obtain ⟨d, hd, B, _, hB⟩ :=
    F.exists_right_curvatureTensorNorm_bound_on_component_of_bounded_ancient_zero_volume
      hM04 p hc.2 (by simpa only [interior_Ioo] using hsub.trans hJ)
      (fun t ht => hcomplete t (hJ (hsub ht)))
      (fun t ht x _ => hcurv t (hJ (hsub ht)) x)
      ⟨K, hK, fun x _ => hb x⟩
  exact ⟨d, hd, B, hB⟩

end PoincareConjecture
