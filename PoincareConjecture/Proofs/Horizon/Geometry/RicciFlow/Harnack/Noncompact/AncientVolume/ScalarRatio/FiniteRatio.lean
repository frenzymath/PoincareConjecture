import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.PositiveRatioContradiction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.FiniteRatioSequence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]



theorem false_of_positive_finite_scalar_ratio
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    (hd : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    {A C L : ℝ} (hA : 0 < A) (hCnonneg : 0 ≤ C)
    (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A))
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    False := by
  apply F.false_of_positive_finite_scalar_ratio_and_corresponding_side_comparison
    hC hcomplete hoperator hK hbound hκ hnoncollapse hn t₀ ht₀ p q hQ hd
    hA hCnonneg hratio hdecay
  intro a b ha hb α β hα0 hβ0 hα hβ
  exact (F.metric t₀).toponogov_corresponding_side_of_edist_segments
    (F.connection t₀) (hcomplete t₀ ht₀)
    (fun x v w => (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w) ha hb hα0 hβ0 hα hβ



theorem quadratic_decay_of_finite_scalar_ratio
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ x : M, 0 < (F.connection 0).scalarCurvature x)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hfinite : ¬ ∀ L A : ℝ, ∃ x : M,
      L < ((F.metric t₀).edist p x).toReal ∧
      A < (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2) :
    ∀ C : ℝ, 0 < C → ∃ L : ℝ, 0 < L ∧ ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C := by
  obtain ⟨A, hA, q, hQ, hd, hratio, htail⟩ :=
    F.exists_finite_scalar_ratio_sequence_of_bounded_ancient hC hcomplete hoperator
      hK hbound hnonflat t₀ ht₀ p hfinite
  rcases hA.eq_or_lt with hzero | hpositive
  · intro C hCpos
    exact htail C (by linarith)
  · obtain ⟨L, _hL, hdecay⟩ := htail (A + 1) (by linarith)
    exact (F.false_of_positive_finite_scalar_ratio hC hcomplete hoperator hK hbound
      hκ hnoncollapse hn t₀ ht₀ p q hQ hd hpositive (by linarith : 0 ≤ A + 1)
      hratio hdecay).elim

end PoincareConjecture.RicciFlow
