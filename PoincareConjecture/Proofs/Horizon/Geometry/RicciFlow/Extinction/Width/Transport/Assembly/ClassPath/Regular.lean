import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath.Data
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath.Finite
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.SlabCoherence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology unitInterval

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
  (H : RepairedAncestryTransportInput D W P K C)
  (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})

noncomputable def m67RegularClassDatumLE
    (a b : Set.Icc (0 : ℝ) T) (hab : a ≤ b)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1))
    (x : M67ClassDatum S (P.component a)) : M67ClassDatum S (P.component b) :=
  if heq : a = b then heq ▸ x else
    m67RegularClassDatum H S B a b
      (lt_of_le_of_ne hab (fun h => heq (Subtype.ext h))) hJ x

theorem m67RegularClassDatumLE_refl
    (a : Set.Icc (0 : ℝ) T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 a.1))
    (x : M67ClassDatum S (P.component a)) :
    m67RegularClassDatumLE H S B a a le_rfl hJ x = x := by
  simp [m67RegularClassDatumLE]

theorem m67RegularClassDatumLE_of_lt
    (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1))
    (x : M67ClassDatum S (P.component a)) :
    m67RegularClassDatumLE H S B a b hab.le hJ x =
      m67RegularClassDatum H S B a b hab hJ x := by
  simp [m67RegularClassDatumLE, ne_of_lt (show a < b from hab)]

theorem m67RegularClassDatum_comp
    (a b c : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (hJab : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1))
    (hJbc : Disjoint D.flow.surgery_times (Set.Ioc b.1 c.1))
    (hJac : Disjoint D.flow.surgery_times (Set.Ioc a.1 c.1))
    (x : M67ClassDatum S (P.component a)) :
    m67RegularClassDatum H S B b c hbc hJbc
        (m67RegularClassDatum H S B a b hab hJab x) =
      m67RegularClassDatum H S B a c (hab.trans hbc) hJac x := by
  let y := m67RegularClassDatum H S B a b hab hJab x
  let z := m67RegularClassDatum H S B b c hbc hJbc y
  have htrans := m67_alpha_transport_trans B
    (m67RegularClassDatum_transport H S B a b hab hJab x)
    (m67RegularClassDatum_transport H S B b c hbc hJbc y)
  have hmap : (repairedDiffeomorphContinuousMap (P.regular_transport b c hbc hJbc)).comp
      (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hJab)) =
      repairedDiffeomorphContinuousMap (P.regular_transport a c (hab.trans hbc) hJac) := by
    ext p
    exact m67_regular_transport_comp P a b c hab hbc hJab hJbc hJac p
  rw [hmap] at htrans
  apply M67ClassDatum.ext
  exact m67_alpha_transport_unique S B (P.regular_transport a c (hab.trans hbc) hJac).contMDiff
    (S.core (P.component a).compact (P.component a).connected
      (P.component a).basepoint x.pi_two_trivial)
    (S.core (P.component c).compact (P.component c).connected
      (P.component c).basepoint z.pi_two_trivial) htrans
    (m67RegularClassDatum_transport H S B a c (hab.trans hbc) hJac x)

theorem m67RegularClassDatumLE_comp
    (a b c : Set.Icc (0 : ℝ) T) (hab : a ≤ b) (hbc : b ≤ c)
    (hJab : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1))
    (hJbc : Disjoint D.flow.surgery_times (Set.Ioc b.1 c.1))
    (hJac : Disjoint D.flow.surgery_times (Set.Ioc a.1 c.1))
    (x : M67ClassDatum S (P.component a)) :
    m67RegularClassDatumLE H S B b c hbc hJbc
        (m67RegularClassDatumLE H S B a b hab hJab x) =
      m67RegularClassDatumLE H S B a c (hab.trans hbc) hJac x := by
  by_cases heq : a = b
  · subst b
    rw [m67RegularClassDatumLE_refl]
  by_cases heq' : b = c
  · subst c
    rw [m67RegularClassDatumLE_refl]
  have hab' : a.1 < b.1 := lt_of_le_of_ne hab (fun h => heq (Subtype.ext h))
  have hbc' : b.1 < c.1 := lt_of_le_of_ne hbc (fun h => heq' (Subtype.ext h))
  rw [m67RegularClassDatumLE_of_lt H S B a b hab',
    m67RegularClassDatumLE_of_lt H S B b c hbc',
    m67RegularClassDatumLE_of_lt H S B a c (hab'.trans hbc')]
  exact m67RegularClassDatum_comp H S B a b c hab' hbc' hJab hJbc hJac x

theorem m67_ordinaryBetween_surgery_disjoint
    {events : Finset (Set.Icc (0 : ℝ) T)}
    (hevents : ∀ t : Set.Icc (0 : ℝ) T, t ∈ events ↔ t.1 ∈ D.flow.surgery_times)
    {a b : Set.Icc (0 : ℝ) T} (h : M67OrdinaryBetween events a b) :
    Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1) := by
  apply Set.disjoint_left.mpr
  intro t ht htab
  let ti : Set.Icc (0 : ℝ) T :=
    ⟨t, a.2.1.trans htab.1.le, htab.2.trans b.2.2⟩
  exact Set.disjoint_left.mp h.2 ((hevents ti).mpr ht) htab

noncomputable def m67OrdinaryClassDatum
    {events : Finset (Set.Icc (0 : ℝ) T)}
    (hevents : ∀ t : Set.Icc (0 : ℝ) T, t ∈ events ↔ t.1 ∈ D.flow.surgery_times)
    (a b : Set.Icc (0 : ℝ) T) (h : M67OrdinaryBetween events a b) :
    M67ClassDatum S (P.component a) → M67ClassDatum S (P.component b) :=
  m67RegularClassDatumLE H S B a b h.1 (m67_ordinaryBetween_surgery_disjoint hevents h)

theorem m67OrdinaryClassDatum_refl
    {events : Finset (Set.Icc (0 : ℝ) T)}
    (hevents : ∀ t : Set.Icc (0 : ℝ) T, t ∈ events ↔ t.1 ∈ D.flow.surgery_times)
    (a : Set.Icc (0 : ℝ) T) (h : M67OrdinaryBetween events a a)
    (x : M67ClassDatum S (P.component a)) :
    m67OrdinaryClassDatum H S B hevents a a h x = x :=
  m67RegularClassDatumLE_refl H S B a _ x

theorem m67OrdinaryClassDatum_trans
    {events : Finset (Set.Icc (0 : ℝ) T)}
    (hevents : ∀ t : Set.Icc (0 : ℝ) T, t ∈ events ↔ t.1 ∈ D.flow.surgery_times)
    (a b c : Set.Icc (0 : ℝ) T)
    (hab : M67OrdinaryBetween events a b) (hbc : M67OrdinaryBetween events b c)
    (x : M67ClassDatum S (P.component a)) :
    m67OrdinaryClassDatum H S B hevents b c hbc
        (m67OrdinaryClassDatum H S B hevents a b hab x) =
      m67OrdinaryClassDatum H S B hevents a c (hab.trans hbc) x :=
  m67RegularClassDatumLE_comp H S B a b c hab.1 hbc.1 _ _ _ x

end PoincareConjecture
