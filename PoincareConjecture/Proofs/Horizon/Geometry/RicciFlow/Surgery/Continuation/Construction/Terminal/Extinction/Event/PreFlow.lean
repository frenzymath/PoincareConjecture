import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Nonempty
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedPreterminalSlab

variable {F : SurgeryFlowData.{u}} {T : ℝ} (S : RepairedPreterminalSlab F T)

def rebaseFlow (r : Ico S.start T) :
    RicciFlow 3 (F.slice r.1).carrier (Ico r.1 T) := by
  let H := S.flow.pullbackDiffeomorph (S.identify r).symm
  apply Poincare.Geometry.RicciFlow.Harnack.restrictFlow H
    (Ico_subset_Ico_left r.2.1) ordConnected_Ico
  obtain ⟨s, hrs, hsT⟩ := exists_between r.2.2
  exact ⟨r.1, ⟨le_rfl, r.2.2⟩, s, ⟨hrs.le, hsT⟩, hrs.ne⟩

def rebaseIdentify (r : Ico S.start T) (t : Ico r.1 T) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice r.1).carrier (F.slice t.1).carrier ∞ :=
  (S.identify r).symm.trans (S.identify ⟨t.1, r.2.1.trans t.2.1, t.2.2⟩)

@[simp] theorem rebaseIdentify_initial (r : Ico S.start T) (x : (F.slice r.1).carrier) :
    S.rebaseIdentify r ⟨r.1, le_rfl, r.2.2⟩ x = x :=
  (S.identify r).apply_symm_apply x

theorem rebaseIdentify_source (r : Ico S.start T) (t : Ico r.1 T)
    (x : (F.slice S.start).carrier) :
    S.rebaseIdentify r t (S.identify r x) =
      S.identify ⟨t.1, r.2.1.trans t.2.1, t.2.2⟩ x := by
  change S.identify _ ((S.identify r).symm (S.identify r x)) = _
  rw [Diffeomorph.symm_apply_apply]

theorem rebase_nonempty (r : Ico S.start T) : Nonempty (F.slice r.1).carrier := by
  obtain ⟨x⟩ := S.start_nonempty
  exact ⟨S.identify r x⟩

theorem rebase_transport (r : Ico S.start T) (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico r.1 T) (ht' : t ∈ Ico r.1 T) (x : (F.slice r.1).carrier) :
    (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
        (S.rebaseIdentify r ⟨s, hs'⟩ x) = S.rebaseIdentify r ⟨t, ht'⟩ x :=
  S.transport_compatibility a b hab hJ hfree s t hs ht
    ⟨r.2.1.trans hs'.1, hs'.2⟩ ⟨r.2.1.trans ht'.1, ht'.2⟩ ((S.identify r).symm x)

theorem rebaseFlow_inner (r : Ico S.start T) (t : ℝ)
    (x : (F.slice r.1).carrier) (v w : TangentSpace (𝓡 3) x) :
    ((S.rebaseFlow r).metric t).inner x v w =
      (S.flow.metric t).inner ((S.identify r).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (S.identify r).symm x v)
        (mfderiv (𝓡 3) (𝓡 3) (S.identify r).symm x w) := rfl

theorem rebaseFlow_scalar (r : Ico S.start T) (t : ℝ) (x : (F.slice r.1).carrier) :
    ((S.rebaseFlow r).connection t).scalarCurvature x =
      (S.flow.connection t).scalarCurvature ((S.identify r).symm x) :=
  S.flow.pullbackDiffeomorph_scalarCurvature (S.identify r).symm t x

theorem rebase_metric (r : Ico S.start T) (t : Ico r.1 T)
    (x : (F.slice r.1).carrier) (v w : TangentSpace (𝓡 3) x) :
    (F.metric t.1).inner (S.rebaseIdentify r t x)
      (mfderiv (𝓡 3) (𝓡 3) (S.rebaseIdentify r t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (S.rebaseIdentify r t) x w) =
        ((S.rebaseFlow r).metric t.1).inner x v w := by
  rw [S.rebaseFlow_inner]
  simp only [rebaseIdentify, Diffeomorph.coe_trans]
  rw [mfderiv_comp x
    ((S.identify _).contMDiff.mdifferentiable (by simp) _)
    ((S.identify r).symm.contMDiff.mdifferentiable (by simp) _)]
  exact S.metric_pullback ⟨t.1, r.2.1.trans t.2.1, t.2.2⟩ ((S.identify r).symm x)
    (mfderiv (𝓡 3) (𝓡 3) (S.identify r).symm x v)
    (mfderiv (𝓡 3) (𝓡 3) (S.identify r).symm x w)

theorem rebaseFlow_source_metric (r : Ico S.start T) (t : ℝ)
    (x : (F.slice S.start).carrier) (v w : TangentSpace (𝓡 3) x) :
    ((S.rebaseFlow r).metric t).inner (S.identify r x)
      (mfderiv (𝓡 3) (𝓡 3) (S.identify r) x v)
      (mfderiv (𝓡 3) (𝓡 3) (S.identify r) x w) =
        (S.flow.metric t).inner x v w := by
  let e := S.identify r
  have hcomp : e.symm ∘ e = id := funext e.symm_apply_apply
  have hd := mfderiv_comp x (e.symm.contMDiff.mdifferentiable (by simp) (e x))
    (e.contMDiff.mdifferentiable (by simp) x)
  rw [hcomp, mfderiv_id] at hd
  have hv (a : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x a) = a :=
    (congrArg (fun D => D a) hd).symm
  rw [S.rebaseFlow_inner]
  change (S.flow.metric t).inner (e.symm (e x))
    (mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v))
    (mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w)) = _
  rw [hv, hv, e.symm_apply_apply]

end PoincareConjecture.RepairedPreterminalSlab

namespace PoincareConjecture.RepairedContinuationInput

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)

def vanishingReference : ℝ :=
  (max I.last_slab.start (T - F.parameters.h T ^ 2) + T) / 2

theorem vanishingReference_bounds :
    I.last_slab.start < I.vanishingReference ∧ I.vanishingReference < T ∧
      T - F.parameters.h T ^ 2 < I.vanishingReference := by
  have hh : 0 < F.parameters.h T ^ 2 :=
    sq_pos_of_pos (F.parameters.h_pos T I.terminal_pos.le)
  have hmax : max I.last_slab.start (T - F.parameters.h T ^ 2) < T :=
    max_lt I.last_slab.start_lt (by linarith)
  dsimp [vanishingReference]
  constructor
  · linarith [le_max_left I.last_slab.start (T - F.parameters.h T ^ 2)]
  constructor
  · linarith
  · linarith [le_max_right I.last_slab.start (T - F.parameters.h T ^ 2)]

def vanishingReferenceTime : Ico I.last_slab.start T :=
  ⟨I.vanishingReference, I.vanishingReference_bounds.1.le, I.vanishingReference_bounds.2.1⟩

end PoincareConjecture.RepairedContinuationInput
