import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.WidthComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.MetricCalibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.ScalarInfimum

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem m67_regular_width_agreement
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    (P : RepairedComponentPath D.flow T W)
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (hM61 : M61WidthTheory.{u} S.quotient)
    (slice : ∀ s, M67WidthSlice S.quotient (P.component s))
    (hambient : ∀ s, (slice s).ambient_metric = D.flow.metric s.1)
    (hclass : ∀ (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1)),
      M67AlphaTransport B (P.component a).basepoint (P.component b).basepoint
        (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hJ))
        (slice a).alpha (slice b).alpha)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
    (s : Set.Icc a b) :
    m61BasedClassWidth S.quotient
      (slice ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩).metric
      (P.component ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩).basepoint
      (slice ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩).alpha =
        m66Width (m67RegularInputOfSlice
          (P.component ⟨a, ha, hab.le.trans hb⟩)
          (slice ⟨a, ha, hab.le.trans hb⟩) hab
          (repairedRegularFlow D P ha hab hb hJ)) s := by
  let aI : Set.Icc (0 : ℝ) T := ⟨a, ha, hab.le.trans hb⟩
  let sI : Set.Icc (0 : ℝ) T := ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩
  let F := repairedRegularFlow D P ha hab hb hJ
  have hmetric (t : Set.Icc (0 : ℝ) T) (x v w) :
      (D.flow.metric t.1).inner ((P.component t).inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) (P.component t).inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3) (P.component t).inclusion x w) =
      (slice t).metric.inner x v w := by
    rw [← hambient t]
    exact (slice t).metric_pullback x v w
  have hfree := (hM61.based_class (F.metric s.1) (P.component aI).compact
    (P.component aI).connected (P.component aI).basepoint
    (slice aI).pi_two_trivial (slice aI).alpha).eq_free
    (slice aI).family (slice aI).family_null (slice aI).represents
  change m61BasedClassWidth S.quotient (slice sI).metric (P.component sI).basepoint
    (slice sI).alpha = m61FreeClassWidth (F.metric s.1) (slice aI).family
  rw [← hfree]
  by_cases has : a < s.1
  · have hJs : Disjoint D.flow.surgery_times (Set.Ioc a s.1) :=
      hJ.mono_right (show Set.Ioc a s.1 ⊆ Set.Ioc a b from
        fun _ hu => ⟨hu.1, hu.2.trans s.2.2⟩)
    exact m67_based_width_eq_of_diffeomorph S B hM61 (F.metric s.1) (slice sI).metric
      (P.component aI).compact (P.component sI).compact
      (P.component aI).connected (P.component sI).connected
      (P.component aI).basepoint (P.component sI).basepoint
      (slice aI).pi_two_trivial (slice sI).pi_two_trivial
      (P.regular_transport aI sI has hJs)
      (m67_regular_flow_metric_at D P ha hab hb hJ s has hJs
        (slice sI).metric (hmetric sI))
      (slice aI).alpha (slice sI).alpha (hclass aI sI has hJs)
  · have hsa : s.1 = a := le_antisymm (le_of_not_gt has) s.2.1
    have hsI : sI = aI := Subtype.ext hsa
    rw [hsI, hsa]
    apply m67_based_width_eq_of_diffeomorph S B hM61 (F.metric a) (slice aI).metric
      (P.component aI).compact (P.component aI).compact
      (P.component aI).connected (P.component aI).connected
      (P.component aI).basepoint (P.component aI).basepoint
      (slice aI).pi_two_trivial (slice aI).pi_two_trivial
      (Diffeomorph.refl (𝓡 3) (P.component aI).carrier.carrier ∞)
      _ (slice aI).alpha (slice aI).alpha
      (m67_alpha_transport_refl B (P.component aI).basepoint (slice aI).alpha)
    intro x v w
    change (F.metric a).inner x v w = (slice aI).metric.inner x
      (mfderiv (𝓡 3) (𝓡 3) id x v) (mfderiv (𝓡 3) (𝓡 3) id x w)
    rw [mfderiv_id]
    exact m67_regular_flow_initial_metric D P ha hab hb hJ (slice aI).metric
      (hmetric aI) x v w

end PoincareConjecture
