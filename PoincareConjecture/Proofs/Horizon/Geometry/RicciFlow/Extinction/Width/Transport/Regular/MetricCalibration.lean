import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.SlabCoherence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.RegularFlowBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem m67_slab_initial_metric
    {F : SurgeryFlowData.{u}} {a b : ℝ}
    (slab : SurgeryRegularSlab F.slice F.metric a b)
    (x : (F.slice a).carrier) (v w : TangentSpace (𝓡 3) x) :
    (slab.flow.metric a).inner x v w = (F.metric a).inner x v w := by
  have hid : slab.identify ⟨a, le_rfl, slab.ordered.le⟩ =
      Diffeomorph.refl (𝓡 3) (F.slice a).carrier ∞ := by
    ext z
    exact slab.initial_identify z
  have h := slab.metric_pullback ⟨a, le_rfl, slab.ordered.le⟩ x v w
  rw [hid] at h
  simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id,
    ContinuousLinearMap.id_apply] using h.symm

theorem m67_regular_flow_initial_metric
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    (P : RepairedComponentPath D.flow T W)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
    (g : RiemannianMetric 3 (P.component ⟨a, ha, hab.le.trans hb⟩).carrier.carrier)
    (hmetric : ∀ x v w, (D.flow.metric a).inner
      ((P.component ⟨a, ha, hab.le.trans hb⟩).inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) (P.component ⟨a, ha, hab.le.trans hb⟩).inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) (P.component ⟨a, ha, hab.le.trans hb⟩).inclusion x w) =
        g.inner x v w)
    (x : (P.component ⟨a, ha, hab.le.trans hb⟩).carrier.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    ((repairedRegularFlow D P ha hab hb hJ).metric a).inner x v w = g.inner x v w := by
  rw [repairedRegularFlow_metric D P ha hab hb hJ ⟨a, le_rfl, hab.le⟩]
  rw [m67_slab_initial_metric]
  exact hmetric x v w



theorem m67_regular_flow_metric_at
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    (P : RepairedComponentPath D.flow T W)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
    (s : Set.Icc a b) (has : a < s.1)
    (hJs : Disjoint D.flow.surgery_times (Set.Ioc a s.1))
    (g : RiemannianMetric 3
      (P.component ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩).carrier.carrier)
    (hmetric : ∀ y v w, (D.flow.metric s.1).inner
      ((P.component ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩).inclusion y)
      (mfderiv (𝓡 3) (𝓡 3)
        (P.component ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩).inclusion y v)
      (mfderiv (𝓡 3) (𝓡 3)
        (P.component ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩).inclusion y w) =
          g.inner y v w)
    (x : (P.component ⟨a, ha, hab.le.trans hb⟩).carrier.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    let e := P.regular_transport ⟨a, ha, hab.le.trans hb⟩
      ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩ has hJs
    ((repairedRegularFlow D P ha hab hb hJ).metric s.1).inner x v w =
      g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  let aI : Set.Icc (0 : ℝ) T := ⟨a, ha, hab.le.trans hb⟩
  let bI : Set.Icc (0 : ℝ) T := ⟨b, ha.trans hab.le, hb⟩
  let sI : Set.Icc (0 : ℝ) T := ⟨s.1, ha.trans s.2.1, s.2.2.trans hb⟩
  let C₀ := P.component aI
  let Cs := P.component sI
  let slab := D.flow.regular_slabs a b hab
    (fun _u hu => P.time_subset ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ
  let e := P.regular_transport aI sI has hJs
  have hid : (slab.identify ⟨a, le_rfl, hab.le⟩ :
      (D.flow.slice a).carrier → (D.flow.slice a).carrier) = id :=
    funext slab.initial_identify
  have hsymm (z : (D.flow.slice a).carrier) :
      (slab.identify ⟨a, le_rfl, hab.le⟩).symm z = z := by
    have h := (slab.identify ⟨a, le_rfl, hab.le⟩).apply_symm_apply z
    rwa [hid, id_eq] at h
  have hmap : Cs.inclusion ∘ e = (slab.identify s) ∘ C₀.inclusion := by
    funext z
    have h := m67_regular_transport_ambient_in_slab P aI bI hab hJ aI sI has hJs
      ⟨le_rfl, hab.le⟩ s.2 z
    change Cs.inclusion (e z) = slab.identify s
      ((slab.identify ⟨a, le_rfl, hab.le⟩).symm (C₀.inclusion z)) at h
    rw [hsymm] at h
    exact h
  have hderiv := congrArg (fun f : C₀.carrier.carrier → (D.flow.slice s.1).carrier =>
      (D.flow.metric s.1).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)) hmap
  rw [mfderiv_comp x (Cs.inclusion_smooth.mdifferentiable (by simp) (e x))
      (e.contMDiff.mdifferentiable (by simp) x),
    mfderiv_comp x ((slab.identify s).contMDiff.mdifferentiable (by simp) (C₀.inclusion x))
      (C₀.inclusion_smooth.mdifferentiable (by simp) x)] at hderiv
  change (D.flow.metric s.1).inner (Cs.inclusion (e x))
      (mfderiv (𝓡 3) (𝓡 3) Cs.inclusion (e x) (mfderiv (𝓡 3) (𝓡 3) e x v))
      (mfderiv (𝓡 3) (𝓡 3) Cs.inclusion (e x) (mfderiv (𝓡 3) (𝓡 3) e x w)) =
    (D.flow.metric s.1).inner (slab.identify s (C₀.inclusion x))
      (mfderiv (𝓡 3) (𝓡 3) (slab.identify s) (C₀.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C₀.inclusion x v))
      (mfderiv (𝓡 3) (𝓡 3) (slab.identify s) (C₀.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C₀.inclusion x w)) at hderiv
  rw [hmetric, slab.metric_pullback] at hderiv
  exact hderiv.symm

end PoincareConjecture
