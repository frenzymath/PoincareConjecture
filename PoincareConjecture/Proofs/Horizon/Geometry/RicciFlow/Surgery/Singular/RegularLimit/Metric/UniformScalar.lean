import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

theorem tendstoUniformlyOn_scalarCurvature
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {T : ℝ} (hT : T ∈ J)
    {K : Set M} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t x => (F.connection t).scalarCurvature x)
      (F.connection T).scalarCurvature (𝓝[J] T) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨V, hV, hbound⟩ := hK.mem_uniformity_of_prod
    (f := fun t x => (F.connection t).scalarCurvature x)
    (F.contMDiffOn_scalarCurvature.continuousOn.mono
      (prod_mono subset_rfl (subset_univ K))) hT (Metric.dist_mem_uniformity hε)
  filter_upwards [hV] with t ht x hx
  have hb : dist ((F.connection t).scalarCurvature x)
      ((F.connection T).scalarCurvature x) < ε := hbound t ht x hx
  rwa [dist_comm] at hb

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalFlow_scalar_of_ne
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ≠ T) (x : H.regularRegion P04) :
    ((H.terminalFlow P04).connection t).scalarCurvature x = H.reference.scalar t x := by
  apply ((H.terminalFlow P04).connection t).scalarCurvature_eq_of_local_isometry
    (H.reference.flow.connection t) (f := Subtype.val) isOpen_univ
    (contMDiff_subtype_val.contMDiffOn) (hx := mem_univ x)
  intro y _ v w
  rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
  exact H.terminalMetricFamily_inner_of_ne P04 ht y v w

theorem terminalFlow_scalar_at_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) :
    ((H.terminalFlow P04).connection T).scalarCurvature x =
      (H.terminalConnection P04).scalarCurvature x :=
  congrArg (fun g : RiemannianMetric 3 (H.regularRegion P04) =>
    g.leviCivitaData.scalarCurvature x) (H.terminalMetricFamily_at_terminal P04)

theorem tendstoUniformlyOn_terminal_scalarCurvature
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {K : Set (H.regularRegion P04)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t (x : H.regularRegion P04) => H.reference.scalar t x)
      (H.terminalConnection P04).scalarCurvature (𝓝[<] T) K := by
  have hfilter : 𝓝[<] T ≤ 𝓝[Ioc H.reference.tMinus T] T :=
    nhdsWithin_le_of_mem (Ioc_mem_nhdsLT H.reference.tMinus_lt)
  have h := ((H.terminalFlow P04).tendstoUniformlyOn_scalarCurvature
    ⟨H.reference.tMinus_lt, le_rfl⟩ hK)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hfilter (Metric.tendstoUniformlyOn_iff.mp h ε hε),
    self_mem_nhdsWithin] with t ht htT
  intro x hx
  simpa only [H.terminalFlow_scalar_at_terminal P04 x,
    H.terminalFlow_scalar_of_ne P04 (ne_of_lt htT) x] using ht x hx

end PoincareConjecture.SingularTimeAssumptions
