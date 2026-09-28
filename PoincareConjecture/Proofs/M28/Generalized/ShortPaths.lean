import PoincareConjecture.Statements.M28Providers
import PoincareConjecture.Proofs.M09.TensorTrace
import PoincareConjecture.Proofs.M28.Mathlib.LastLevel










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




theorem RiemannianMetric.exists_short_path_of_mem_ball
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {x y : M} {r : ℝ} (hy : y ∈ g.ball x r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ ContMDiff 𝓘(ℝ) (𝓡 n) 1 γ ∧
      g.pathELength γ 0 1 < ENNReal.ofReal r ∧
      γ =ᶠ[𝓝 0] (fun _ ↦ x) ∧ γ =ᶠ[𝓝 1] (fun _ ↦ y) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one




theorem GeneralizedRicciFlowData.continuous_scalar_slice
    (F : GeneralizedRicciFlowData.{u}) (P : RicciFlowCurvatureTheory.{u}) (t : ℝ) :
    Continuous (fun x : (F.slice t).carrier ↦ F.scalar ⟨t, x⟩) := by
  exact (Proofs.M09.tensorMetricTrace_smooth (F.metric t) (F.connection t).ricciEvaluation
    (P.tensor_calculus 3 (F.slice t).carrier (F.metric t) (F.connection t)).2.1).continuous




theorem generalizedSliceStrongCanonicalNeighborhoods.path_last_level
    {F : GeneralizedRicciFlowData.{u}} (P : RicciFlowCurvatureTheory.{u})
    {epsilon C Q t : ℝ}
    (hcanonical : generalizedSliceStrongCanonicalNeighborhoods F epsilon C Q t)
    (γ : ℝ → (F.slice t).carrier) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hstart : F.scalar ⟨t, γ 0⟩ ≤ Q) (hend : Q < F.scalar ⟨t, γ 1⟩) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, F.scalar ⟨t, γ s⟩ = Q ∧
      ∀ v ∈ Set.Icc s 1,
        Nonempty (GeneralizedCanonicalControl (F := F) t (γ v) epsilon C) := by
  have hscalar : ContinuousOn (fun v ↦ F.scalar ⟨t, γ v⟩) (Set.Icc 0 1) :=
    (F.continuous_scalar_slice P t).comp_continuousOn hγ
  obtain ⟨s, hs, heq, hafter⟩ :=
    exists_last_eq_of_continuousOn zero_le_one hscalar hstart hend
  refine ⟨s, hs, heq, ?_⟩
  intro v hv
  apply hcanonical
  rcases eq_or_lt_of_le hv.1 with hvs | hvs
  · simpa [← hvs] using heq.ge
  · exact (hafter v ⟨hvs, hv.2⟩).le

end PoincareConjecture
