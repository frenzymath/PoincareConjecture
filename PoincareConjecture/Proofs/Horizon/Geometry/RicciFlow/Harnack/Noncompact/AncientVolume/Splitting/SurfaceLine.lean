import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Main
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SurfaceFlatness
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric



theorem surface_curvature_eq_zero_of_minimizing_line
    {S : Type u} [TopologicalSpace S] [T3Space S] [ConnectedSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (g : RiemannianMetric 2 S) (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature)
    (γ : ℝ → S)
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    (∀ x, D.scalarCurvature x = 0) ∧
      (∀ x, ∀ a b c d : TangentSpace (𝓡 2) x, D.curvatureTensor x a b c d = 0) ∧
      ∀ x, D.curvatureTensorNorm x = 0 := by
  obtain ⟨hsmooth, hunit, hparallel, _, _⟩ :=
    g.busemann_parallel_unit_gradient D hcomplete hRic hγ
  let V := D.gradient (g.busemann γ)
  have hnonzero (x : S) : V x ≠ 0 := by
    intro hzero
    have hu := hunit x
    change g.inner x (V x) (V x) = 1 at hu
    rw [hzero, map_zero] at hu
    exact zero_ne_one hu
  have hnull := D.curvature_eq_zero_of_constant_covariantDerivative hD V
    (D.contMDiff_gradient hsmooth) 0 (by simpa only [zero_smul] using hparallel)
  have htensor (x : S) (a b c d : TangentSpace (𝓡 2) x) :
      D.curvatureTensor x a b c d = 0 :=
    D.curvatureTensor_eq_zero_of_curvature_null_vector x (V x) (hnonzero x) (hnull x) a b c d
  refine ⟨fun x => D.scalarCurvature_eq_zero_of_curvature_null_vector
    x (V x) (hnonzero x) (hnull x), htensor, ?_⟩
  intro x
  simp only [LeviCivitaData.curvatureTensorNorm, htensor, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, Real.sqrt_zero]

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow



theorem not_minimizing_line_of_bounded_ancient_surface
    {S : Type u} [TopologicalSpace S] [T3Space S]
    [SecondCountableTopology S] [ConnectedSpace S] [NoncompactSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 2 S (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : S, 0 < (F.connection 0).scalarCurvature p)
    {t : ℝ} (ht : t ≤ 0) (γ : ℝ → S) :
    ¬ ∀ s r : ℝ, (F.metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r| := by
  intro hγ
  have hD := hC.tensor_calculus 2 S (F.metric t) (F.connection t)
  have hflat := (F.metric t).surface_curvature_eq_zero_of_minimizing_line
    (F.connection t) hD (hcomplete t ht)
    (fun x v => ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      hD x (hoperator t ht x) v).1) γ hγ
  have hpos := F.scalarCurvature_pos_of_bounded_ancient
    hC hcomplete hoperator hK hbound hnonflat t ht (γ 0)
  rw [hflat.1 (γ 0)] at hpos
  exact lt_irrefl _ hpos

end PoincareConjecture.RicciFlow
