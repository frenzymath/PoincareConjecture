import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Slabs
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Surgery.Splice

open SurgeryEventRebuild

def constantSlab {C : GeneralizedSliceCarrier.{u}} {J : Set ℝ}
    (R : RicciFlow 3 C.carrier J) {a b : ℝ} (hab : a < b)
    (hJ : Set.Icc a b ⊆ J) :
    SurgeryRegularSlab (fun _ => C) R.metric a b where
  ordered := hab
  flow := Poincare.Geometry.RicciFlow.Harnack.restrictFlow R hJ
    Set.ordConnected_Icc ⟨a, ⟨le_rfl, hab.le⟩, b, ⟨hab.le, le_rfl⟩, hab.ne⟩
  identify _ := Diffeomorph.refl (𝓡 3) C.carrier ∞
  initial_identify _ := rfl
  metric_pullback _ _ _ _ := by simp [Poincare.Geometry.RicciFlow.Harnack.restrictFlow]

theorem constantSlab_transport {C : GeneralizedSliceCarrier.{u}} {J : Set ℝ}
    (R : RicciFlow 3 C.carrier J) {a b : ℝ} (hab : a < b)
    (hJ : Set.Icc a b ⊆ J) (s t : Set.Icc a b) (x : C.carrier) :
    (constantSlab R hab hJ).transport s t x = x := rfl

variable (F : SurgeryFlowData.{u}) (T : ℝ) (C : GeneralizedSliceCarrier.{u})
  {B : ℝ≥0∞} (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

def family (t : ℝ) : SliceMetric.{u} :=
  if t < T then ⟨F.slice t, F.metric t⟩ else ⟨C, R.metric t⟩

theorem family_before {t : ℝ} (ht : t < T) :
    family F T C R t = ⟨F.slice t, F.metric t⟩ := if_pos ht

theorem family_after {t : ℝ} (ht : T ≤ t) :
    family F T C R t = ⟨C, R.metric t⟩ := if_neg (not_lt.mpr ht)

def slice (t : ℝ) : GeneralizedSliceCarrier.{u} := (family F T C R t).1

def metric (t : ℝ) : RiemannianMetric 3 (slice F T C R t).carrier :=
  (family F T C R t).2

def identifyBefore (t : ℝ) (ht : t < T) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t).carrier (slice F T C R t).carrier ∞ :=
  identify _ _ (family_before F T C R ht).symm

def identifyAfter (t : ℝ) (ht : T ≤ t) :
    Diffeomorph (𝓡 3) (𝓡 3) C.carrier (slice F T C R t).carrier ∞ :=
  identify _ _ (family_after F T C R ht).symm

def eventTimes : Set ℝ := insert T F.surgery_times


theorem slab_side {a b : ℝ}
    (hfree : Disjoint (eventTimes F T) (Set.Ioc a b)) : b < T ∨ T ≤ a := by
  by_cases hb : b < T
  · exact Or.inl hb
  · right
    by_contra ha
    exact Set.disjoint_left.mp hfree (Set.mem_insert T F.surgery_times)
      ⟨lt_of_not_ge ha, le_of_not_gt hb⟩


def regularSlab (hF : F.time_domain = Set.Ico 0 T)
    {a b : ℝ} (hab : a < b)
    (hJ : Set.Icc a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree : Disjoint (eventTimes F T) (Set.Ioc a b)) :
    SurgeryRegularSlab (slice F T C R) (metric F T C R) a b := by
  classical
  by_cases hb : b < T
  · have hold : Set.Icc a b ⊆ F.time_domain := by
      intro t ht
      rw [hF]
      exact ⟨(hJ ht).1, ht.2.trans_lt hb⟩
    have hfreeold : Disjoint F.surgery_times (Set.Ioc a b) :=
      hfree.mono_left (Set.subset_insert T F.surgery_times)
    let A := F.regular_slabs a b hab hold hfreeold
    exact A.copyFamily (future := family F T C R)
      (fun t ht => (family_before F T C R (ht.2.trans_lt hb)).symm)
  · have ha := (slab_side F T hfree).resolve_left hb
    have hpost : Set.Icc a b ⊆ {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B} :=
      fun t ht => ⟨ha.trans ht.1, (hJ ht).2⟩
    exact (constantSlab R hab hpost).copyFamily (future := family F T C R)
      (fun t ht => (family_after F T C R (ha.trans ht.1)).symm)

theorem regularSlab_transport_before (hF : F.time_domain = Set.Ico 0 T)
    {a b : ℝ} (hab : a < b)
    (hJ : Set.Icc a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree : Disjoint (eventTimes F T) (Set.Ioc a b)) (hb : b < T)
    (hold : Set.Icc a b ⊆ F.time_domain)
    (hfreeold : Disjoint F.surgery_times (Set.Ioc a b))
    (s t : Set.Icc a b) (x : (F.slice s).carrier) :
    (regularSlab F T C R hF hab hJ hfree).transport s t
        (identifyBefore F T C R s (s.property.2.trans_lt hb) x) =
      identifyBefore F T C R t (t.property.2.trans_lt hb)
        ((F.regular_slabs a b hab hold hfreeold).transport s t x) := by
  simp only [regularSlab, dif_pos hb]
  exact SurgeryRegularSlab.copyFamily_transport
    (past := fun t => ⟨F.slice t, F.metric t⟩) (future := family F T C R)
    (F.regular_slabs a b hab hold hfreeold)
    (fun t ht => (family_before F T C R (ht.2.trans_lt hb)).symm) s t x

theorem regularSlab_transport_after (hF : F.time_domain = Set.Ico 0 T)
    {a b : ℝ} (hab : a < b)
    (hJ : Set.Icc a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree : Disjoint (eventTimes F T) (Set.Ioc a b)) (ha : T ≤ a)
    (s t : Set.Icc a b) (x : C.carrier) :
    (regularSlab F T C R hF hab hJ hfree).transport s t
        (identifyAfter F T C R s (ha.trans s.property.1) x) =
      identifyAfter F T C R t (ha.trans t.property.1) x := by
  have hb : ¬ b < T := not_lt.mpr (ha.trans hab.le)
  simp only [regularSlab, dif_neg hb]
  exact SurgeryRegularSlab.copyFamily_transport
    (past := fun t => ⟨C, R.metric t⟩) (future := family F T C R)
    (constantSlab R hab (fun t ht => ⟨ha.trans ht.1, (hJ ht).2⟩))
    (fun t ht => (family_after F T C R (ha.trans ht.1)).symm) s t x

end PoincareConjecture.Surgery.Splice
