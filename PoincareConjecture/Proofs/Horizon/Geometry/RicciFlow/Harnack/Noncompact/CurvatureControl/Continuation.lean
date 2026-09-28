import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.BoundedFlow.Components








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_uniform_curvatureTensorNorm_bound_of_local_right_bound
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) {a b : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hslice : ∀ t ∈ Icc a b, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x)
    (hright : ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
      ∀ t ∈ Icc c d, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ K := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_curvatureTensorNorm_bound_on_set_of_local_right_bound_and_harnack
      hC F univ hab hJ (fun t ht x _ => hcurv t ht x)
      (fun t ht => by
        obtain ⟨K, hK, hb⟩ := hslice t ht
        exact ⟨K, hK, fun x _ => hb x⟩)
      (fun c hc => by
        obtain ⟨d, hd, K, hb⟩ := hright c hc
        exact ⟨d, hd, K, fun t ht x _ => hb t ht x⟩)
      (by
        intro c hc hbounded x _ t ht
        obtain ⟨K, hb⟩ := hbounded
        exact scalar_harnack_on_bounded_slab hC F hc.1
          ((Icc_subset_Icc_right hc.2).trans hJ)
          (fun s hs => hcomplete s ⟨hs.1, hs.2.trans hc.2⟩)
          (fun s hs y => hb s hs y (mem_univ y))
          (fun s hs => hcurv s ⟨hs.1, hs.2.trans hc.2⟩) t ht x)
  exact ⟨K, hK, fun t ht x => hbound t ht x (mem_univ x)⟩



theorem finite_differential_of_local_right_curvature_bounds
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁))
    (hcomplete : ∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Ioo T₀ T₁, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hslice : ∀ t ∈ Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x)
    (hright : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo T₀ T₁ →
      ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
        ∀ t ∈ Icc c d, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  apply finite_differential_of_curvature_slab_bounds hC F hcomplete hcurv
  intro a b hab hJ
  obtain ⟨K, _, hb⟩ := exists_uniform_curvatureTensorNorm_bound_of_local_right_bound
    hC F hab hJ (fun t ht => hcomplete t (hJ ht))
    (fun t ht => hcurv t (hJ ht)) (fun t ht => hslice t (hJ ht))
    (hright a b hab hJ)
  exact ⟨K, hb⟩

omit [PreconnectedSpace M] in

theorem exists_uniform_curvatureTensorNorm_bound_on_component_of_local_right_bound
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) (p : M) {a b : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Icc a b, ∀ x ∈ connectedComponent p,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hslice : ∀ t ∈ Icc a b, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ connectedComponent p,
        LeviCivitaData.CurvatureOperatorBound (F.connection t) K x)
    (hright : ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
      ∀ t ∈ Icc c d, ∀ x ∈ connectedComponent p,
        (F.connection t).curvatureTensorNorm x ≤ K) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x ∈ connectedComponent p,
      (F.connection t).curvatureTensorNorm x ≤ K := by
  apply exists_uniform_curvatureTensorNorm_bound_on_set_of_local_right_bound_and_harnack
    hC F (connectedComponent p) hab hJ hcurv hslice hright
  intro c hc hbounded x hx t ht
  obtain ⟨K, hb⟩ := hbounded
  let G := F.restrictComponent p
  let x' : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p := ⟨x, hx⟩
  have hpos := scalar_harnack_on_bounded_slab hC G hc.1
    ((Icc_subset_Icc_right hc.2).trans hJ)
    (fun s hs => F.restrictComponent_metricComplete p s
      (hcomplete s ⟨hs.1, hs.2.trans hc.2⟩))
    (fun s hs y => by
      rw [F.restrictComponent_curvatureTensorNorm]
      exact hb s hs y y.property)
    (fun s hs y => (F.restrictComponent_nonnegativeCurvatureOperator_iff p s y).mpr
      (hcurv s ⟨hs.1, hs.2.trans hc.2⟩ y y.property)) t ht x'
  have htJ := hJ ⟨ht.1.le, ht.2.le.trans hc.2⟩
  have hD := hC.scalar_evolution n _ (Ioo T₀ T₁) G t htJ x'
  simp only [G, F.restrictComponent_scalarCurvature] at hD
  have heq := (hD.hasDerivAt (isOpen_Ioo.mem_nhds htJ)).unique
    ((hC.scalar_evolution n M (Ioo T₀ T₁) F t htJ x).hasDerivAt
      (isOpen_Ioo.mem_nhds htJ))
  simp only [G, F.restrictComponent_scalarCurvature] at hpos
  rw [heq] at hpos
  exact hpos

omit [PreconnectedSpace M] in


theorem finite_differential_of_component_local_right_curvature_bounds
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁))
    (hcomplete : ∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Ioo T₀ T₁, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hslice : ∀ t ∈ Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x)
    (hright : ∀ p : M, ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo T₀ T₁ →
      ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
        ∀ t ∈ Icc c d, ∀ x ∈ connectedComponent p,
          (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  apply finite_differential_of_component_curvature_slab_bounds hC F hcomplete hcurv
  intro p a b hab hJ
  obtain ⟨K, _, hb⟩ :=
    exists_uniform_curvatureTensorNorm_bound_on_component_of_local_right_bound
      hC F p hab hJ (fun t ht => hcomplete t (hJ ht))
      (fun t ht x _ => hcurv t (hJ ht) x)
      (fun t ht => by
        obtain ⟨K, hK, hb⟩ := hslice t (hJ ht)
        exact ⟨K, hK, fun x _ => hb x⟩) (hright p a b hab hJ)
  exact ⟨K, hb⟩

end Poincare.RicciFlow.Harnack
