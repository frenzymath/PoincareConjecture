import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.Static
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientKappaRoundness

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance



theorem einstein_zero_of_negative
    {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
    (K : AncientKappaSolution 3 M)
    (hnegative : ∀ t < 0, ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      (K.flow.connection t).ricci x v w =
        ((K.flow.connection t).scalarCurvature x / 3) * (K.flow.metric t).inner x v w) :
    ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      (K.flow.connection 0).ricci x v w =
        ((K.flow.connection 0).scalarCurvature x / 3) * (K.flow.metric 0).inner x v w := by
  intro x v w
  have hR : ContinuousOn (fun t => (K.flow.connection t).scalarCurvature x) (Iic 0) :=
    ((H.scalar_regular 3 M (Iic 0) K.flow).comp
      (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun t ht => ⟨ht, mem_univ x⟩)).continuousOn
  have hRic : ContinuousOn (fun t => (K.flow.connection t).ricci x v w) (Iic 0) :=
    fun t ht => (H.ricci_evolution 3 M (Iic 0) K.flow t ht x v w).continuousWithinAt
  have hg : ContinuousOn (fun t => (K.flow.metric t).inner x v w) (Iic 0) :=
    fun t ht => (K.flow.equation t ht x v w).continuousWithinAt
  have heq : EqOn (fun t => (K.flow.connection t).ricci x v w)
      (fun t => ((K.flow.connection t).scalarCurvature x / 3) *
        (K.flow.metric t).inner x v w) (Iio 0) := fun t ht => hnegative t ht x v w
  exact heq.of_subset_closure hRic ((hR.div_const 3).mul hg) Iio_subset_Iic_self
    (by rw [closure_Iio]) (by simp)



theorem isRoundAncientKappaSolution_of_early_pinching [CompactSpace M]
    {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
    (K : AncientKappaSolution 3 M)
    (hearly : ∀ c : ℝ, 1 < c → ∀ t : ℝ, t < 0 → ∃ a : ℝ, a < t ∧
      (letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨(K.flow.metric a).toRiemannianMetric⟩
      ∀ x : M, (K.flow.connection a).ricciComplementTensor
        (H.tensor_calculus 3 M (K.flow.metric a) (K.flow.connection a)) x ∈
          tensorPinchingCone c)) :
    IsRoundAncientKappaSolution K := by
  let hcalculus (s : ℝ) := H.tensor_calculus 3 M (K.flow.metric s) (K.flow.connection s)
  have hnegative (t : ℝ) (ht : t < 0) :
      ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
        (K.flow.connection t).ricci x v w =
          ((K.flow.connection t).scalarCurvature x / 3) * (K.flow.metric t).inner x v w := by
    apply (K.flow.connection t).einstein_of_ricciComplement_mem_all_pinchingCones (hcalculus t)
    intro c hc x
    obtain ⟨a, hat, ha⟩ := hearly c hc t ht
    have ha0 := hat.trans ht
    let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow K.flow
      (show Ico a 0 ⊆ Iic 0 from fun _ hs => hs.2.le)
      ordConnected_Ico
      (show (Ico a 0).Nontrivial from
        ⟨a, ⟨le_rfl, ha0⟩, a / 2, ⟨by linarith, by linarith⟩, by linarith⟩)
    exact ricciComplement_mem_of_initial F hcalculus
      (H.scalar_regular 3 M (Ico a 0) F)
      (fun s hs => H.curvature_evolution 3 M (Ico a 0) F s hs)
      hc.le ha ⟨hat.le, ht⟩ x
  have hzero := einstein_zero_of_negative H K hnegative
  intro t ht
  apply (K.flow.connection t).isRoundMetricSlice_of_einstein (hcalculus t)
    (K.nonnegative_curvature_operator t ht) (K.nonflat t ht)
  rcases lt_or_eq_of_le ht with hlt | rfl
  · exact hnegative t hlt
  · exact hzero

end PoincareConjecture.AncientKappaRoundness
