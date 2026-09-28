import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.Composition

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology unitInterval

universe u

namespace PoincareConjecture

theorem m67_regular_transport_ambient_in_slab
    {F : SurgeryFlowData.{u}} {T : ℝ} {W : RepairedEventChildWitness F}
    (P : RepairedComponentPath F T W)
    (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
    (hJ : Disjoint F.surgery_times (Set.Ioc a.1 b.1))
    (s t : Set.Icc (0 : ℝ) T) (hst : s.1 < t.1)
    (hK : Disjoint F.surgery_times (Set.Ioc s.1 t.1))
    (hs : s.1 ∈ Set.Icc a.1 b.1) (ht : t.1 ∈ Set.Icc a.1 b.1)
    (x : (P.component s).carrier.carrier) :
    (P.component t).inclusion (P.regular_transport s t hst hK x) =
      (F.regular_slabs a.1 b.1 hab
        (fun _u hu => P.time_subset ⟨a.2.1.trans hu.1, hu.2.trans b.2.2⟩) hJ).transport
        ⟨s.1, hs⟩ ⟨t.1, ht⟩ ((P.component s).inclusion x) := by
  rw [P.regular_transport_ambient]
  exact F.slab_transport_coherent s.1 t.1 a.1 b.1 hst _ hK hab _ hJ
    s.1 t.1 ⟨le_rfl, hst.le⟩ ⟨hst.le, le_rfl⟩ hs ht _

theorem m67_regular_transport_comp
    {F : SurgeryFlowData.{u}} {T : ℝ} {W : RepairedEventChildWitness F}
    (P : RepairedComponentPath F T W)
    (a b c : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (hJab : Disjoint F.surgery_times (Set.Ioc a.1 b.1))
    (hJbc : Disjoint F.surgery_times (Set.Ioc b.1 c.1))
    (hJac : Disjoint F.surgery_times (Set.Ioc a.1 c.1))
    (x : (P.component a).carrier.carrier) :
    P.regular_transport b c hbc hJbc (P.regular_transport a b hab hJab x) =
      P.regular_transport a c (hab.trans hbc) hJac x := by
  apply (P.component c).left_inverse.injective
  rw [m67_regular_transport_ambient_in_slab P a c (hab.trans hbc) hJac
    b c hbc hJbc ⟨hab.le, hbc.le⟩ ⟨(hab.trans hbc).le, le_rfl⟩]
  rw [m67_regular_transport_ambient_in_slab P a c (hab.trans hbc) hJac
    a b hab hJab ⟨le_rfl, (hab.trans hbc).le⟩ ⟨hab.le, hbc.le⟩]
  rw [P.regular_transport_ambient]
  simp only [SurgeryRegularSlab.transport, Diffeomorph.symm_apply_apply]

end PoincareConjecture
