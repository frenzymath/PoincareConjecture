import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas.TimeWindows

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}

namespace OrdinaryTimeWindow

variable (A : OrdinaryTimeWindow W)

def slab : SurgeryRegularSlab F.slice F.metric A.lower A.upper :=
  F.regular_slabs A.lower A.upper A.ordered (A.slab_subset.trans W.time_subset)
    (A.surgery_free.mono_right Ioc_subset_Icc_self)

def flow : RicciFlow 3 (F.slice A.lower).carrier A.interval where
  metric := A.slab.flow.metric
  connection := A.slab.flow.connection
  interval := A.interval_connected
  nontrivial := A.interval_nontrivial
  smooth := A.slab.flow.smooth.mono (prod_mono A.interval_subset subset_rfl)
  equation t ht x v w :=
    (A.slab.flow.equation t (A.interval_subset ht) x v w).mono A.interval_subset

def identify (t : ℝ) (ht : t ∈ A.interval) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice A.lower).carrier (slice W t).carrier ∞ where
  toFun x := ⟨A.slab.identify ⟨t, A.interval_subset ht⟩ x, A.time_subset ht, by
    rw [m33RegularRegion_of_regular F t (A.regular ht)]
    exact mem_univ _⟩
  invFun x := (A.slab.identify ⟨t, A.interval_subset ht⟩).symm x.val
  left_inv x := (A.slab.identify ⟨t, A.interval_subset ht⟩).symm_apply_apply x
  right_inv x := Subtype.ext ((A.slab.identify ⟨t, A.interval_subset ht⟩).apply_symm_apply x.val)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (regionOpens W t) _).mp
      (A.slab.identify ⟨t, A.interval_subset ht⟩).contMDiff
  contMDiff_invFun :=
    (A.slab.identify ⟨t, A.interval_subset ht⟩).symm.contMDiff.comp (forward_smooth W t)

@[simp] theorem forward_identify (t : ℝ) (ht : t ∈ A.interval)
    (x : (F.slice A.lower).carrier) :
    forward W t (A.identify t ht x) = A.slab.identify ⟨t, A.interval_subset ht⟩ x := rfl

theorem identify_metric (t : ℝ) (ht : t ∈ A.interval)
    (x : (F.slice A.lower).carrier) (v w : TangentSpace (𝓡 3) x) :
    (metric W t).inner (A.identify t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (A.identify t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (A.identify t ht) x w) = (A.flow.metric t).inner x v w := by
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (forward W t) (A.identify t ht x)
        (mfderiv (𝓡 3) (𝓡 3) (A.identify t ht) x z) =
      mfderiv (𝓡 3) (𝓡 3) (A.slab.identify ⟨t, A.interval_subset ht⟩) x z := by
    exact (mfderiv_comp_apply x
      ((forward_smooth W t).mdifferentiable (by simp) _)
      ((A.identify t ht).contMDiff.mdifferentiable (by simp) x) z).symm
  rw [← metric_pullback W t, hderiv v, hderiv w]
  exact A.slab.metric_pullback ⟨t, A.interval_subset ht⟩ x v w

def box : GeneralizedRicciFlowBox (slice W) (metric W) W.interval where
  carrier := F.slice A.lower
  interval := A.interval
  relatively_open := ⟨Ioo A.left A.right, isOpen_Ioo, rfl⟩
  flow := A.flow
  forward t ht := A.identify t ht
  inverse t ht := (A.identify t ht).symm
  forward_openEmbedding t ht := (A.identify t ht).toHomeomorph.isOpenEmbedding
  forward_smooth t ht := (A.identify t ht).contMDiff
  inverse_smooth t ht := (A.identify t ht).symm.contMDiff.contMDiffOn
  left_inverse t ht := (A.identify t ht).symm_apply_apply
  right_inverse t ht _ _ := (A.identify t ht).apply_symm_apply _
  metric_pullback := A.identify_metric

theorem box_forward_surjective (t : ℝ) (ht : t ∈ A.box.interval) :
    Function.Surjective (A.box.forward t ht) := (A.identify t ht).surjective

theorem slab_compatibility (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ A.box.interval) (ht' : t ∈ A.box.interval)
    (x : A.box.carrier.carrier) :
    (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      (forward W s (A.box.forward s hs' x)) =
        forward W t (A.box.forward t ht' x) := by
  change (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      (A.slab.identify ⟨s, A.interval_subset hs'⟩ x) =
        A.slab.identify ⟨t, A.interval_subset ht'⟩ x
  rw [F.slab_transport_coherent a b A.lower A.upper hab hJ hfree
    A.ordered (A.slab_subset.trans W.time_subset)
    (A.surgery_free.mono_right Ioc_subset_Icc_self)
    s t hs ht (A.interval_subset hs') (A.interval_subset ht')]
  exact congrArg (A.slab.identify ⟨t, A.interval_subset ht'⟩)
    ((A.slab.identify ⟨s, A.interval_subset hs'⟩).symm_apply_apply x)

end OrdinaryTimeWindow

theorem ordinary_boxes_vertical_compatibility (A B : OrdinaryTimeWindow W)
    (t : ℝ) (htA : t ∈ A.box.interval) (htB : t ∈ B.box.interval)
    (x : A.box.carrier.carrier) (y : B.box.carrier.carrier)
    (hxy : A.box.forward t htA x = B.box.forward t htB y)
    (s : ℝ) (hsA : s ∈ A.box.interval) (hsB : s ∈ B.box.interval) :
    A.box.forward s hsA x = B.box.forward s hsB y := by
  apply (forward_openEmbedding W s).injective
  have h := B.slab_compatibility A.lower A.upper A.ordered
    (A.slab_subset.trans W.time_subset)
    (A.surgery_free.mono_right Ioc_subset_Icc_self)
    t s (A.interval_subset htA) (A.interval_subset hsA) htB hsB y
  rw [← congrArg (forward W t) hxy] at h
  change A.slab.transport ⟨t, A.interval_subset htA⟩ ⟨s, A.interval_subset hsA⟩
    (A.slab.identify ⟨t, A.interval_subset htA⟩ x) = _ at h
  change A.slab.identify ⟨s, A.interval_subset hsA⟩ x =
    forward W s (B.box.forward s hsB y)
  simpa only [SurgeryRegularSlab.transport, Diffeomorph.symm_apply_apply] using h

theorem ordinary_boxes_cover {t : ℝ} (ht : t ∈ W.interval)
    (hT : t ∉ F.surgery_times) (x : (slice W t).carrier) :
    ∃ A : OrdinaryTimeWindow W, ∃ ht' : t ∈ A.box.interval,
      ∃ y : A.box.carrier.carrier, A.box.forward t ht' y = x := by
  obtain ⟨A, htA⟩ := exists_ordinaryTimeWindow W ht hT
  obtain ⟨y, hy⟩ := A.box_forward_surjective t htA x
  exact ⟨A, htA, y, hy⟩

end PoincareConjecture.Surgery.RegularHistory
