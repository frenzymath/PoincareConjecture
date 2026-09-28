import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.OpenSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Family
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Nonempty

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Extinction

def emptyCarrier (S : GeneralizedSliceCarrier.{u}) : GeneralizedSliceCarrier.{u} :=
  S.openSubset ⊥

instance emptyCarrier_isEmpty (S : GeneralizedSliceCarrier.{u}) :
    IsEmpty (emptyCarrier S).carrier :=
  ⟨fun x => x.property⟩

def emptyMetric {S : GeneralizedSliceCarrier.{u}} (g : RiemannianMetric 3 S.carrier) :
    RiemannianMetric 3 (emptyCarrier S).carrier := S.openSubsetMetric ⊥ g

def emptyFlow {S : GeneralizedSliceCarrier.{u}} (g : RiemannianMetric 3 S.carrier) (T : ℝ) :
    RicciFlow 3 (emptyCarrier S).carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < ⊤} where
  metric _ := emptyMetric g
  connection _ := (emptyMetric g).leviCivitaData
  interval := by
    constructor
    intro a ha b _ x hx
    exact ⟨ha.1.trans hx.1, ENNReal.ofReal_lt_top⟩
  nontrivial := ⟨T, ⟨le_rfl, ENNReal.ofReal_lt_top⟩,
    T + 1, ⟨by linarith, ENNReal.ofReal_lt_top⟩, by linarith⟩
  smooth := by intro p _; exact isEmptyElim p.2
  equation _ _ x := isEmptyElim x

variable (F : SurgeryFlowData.{u}) (T : ℝ)

def slice (t : ℝ) : GeneralizedSliceCarrier.{u} :=
  Splice.slice F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) t

def metric (t : ℝ) : RiemannianMetric 3 (slice F T t).carrier :=
  Splice.metric F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) t

theorem slice_empty_after {t : ℝ} (ht : T ≤ t) : IsEmpty (slice F T t).carrier := by
  change IsEmpty
    (Splice.family F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) t).1.carrier
  rw [Splice.family_after F T _ _ ht]
  exact emptyCarrier_isEmpty _

theorem extinction_permanent (I : RepairedContinuationInput F T)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (he : IsEmpty (slice F T s).carrier) :
    IsEmpty (slice F T t).carrier := by
  have hTs : T ≤ s := by
    by_contra hn
    have hsT : s < T := lt_of_not_ge hn
    have hsF : s ∈ F.time_domain := I.time_domain_eq ▸ (show s ∈ Ico 0 T from ⟨hs, hsT⟩)
    obtain ⟨x⟩ := I.slices_nonempty s hsF
    exact he.false
      (Splice.identifyBefore F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) s hsT x)
  exact slice_empty_after F T (hTs.trans hst)

end PoincareConjecture.Surgery.Extinction
