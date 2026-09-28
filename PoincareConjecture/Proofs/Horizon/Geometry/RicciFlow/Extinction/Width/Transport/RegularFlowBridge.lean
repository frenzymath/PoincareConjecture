import PoincareConjecture.Statements.M67
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.ComponentRestriction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

noncomputable def repairedRegularFlow
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b)) :
    RicciFlow 3
      (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).carrier.carrier
      (Set.Icc a b) :=
  selectedComponentRicciFlow
    (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩)
    (D.flow.regular_slabs a b hab
      (fun _u hu => P.time_subset
        ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ).flow

@[simp] theorem repairedRegularFlow_metric
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
    (s : Set.Icc a b) (x v w) :
    ((repairedRegularFlow D P ha hab hb hJ).metric s.1).inner x v w =
      (((D.flow.regular_slabs a b hab
        (fun _u hu => P.time_subset
          ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ).flow.metric s.1).inner)
        ((P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x)
        (mfderiv (𝓡 3) (𝓡 3)
          (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x w) := by
  rfl

@[simp] theorem repairedRegularFlow_scalarCurvature
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
    (s : Set.Icc a b) (x) :
    ((repairedRegularFlow D P ha hab hb hJ).connection s.1).scalarCurvature x =
      ((D.flow.regular_slabs a b hab
        (fun _u hu => P.time_subset
          ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ).flow.connection s.1).scalarCurvature
        ((P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x) := by
  exact selectedComponentRicciFlow_scalarCurvature
    (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩)
    (D.flow.regular_slabs a b hab
      (fun _u hu => P.time_subset
        ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ).flow s.1 x

end PoincareConjecture
