import PoincareConjecture.Proofs.M47.LimitFinitePhysicalCoherence
import PoincareConjecture.Proofs.M47.LimitFiniteInteriorFlow
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem limitFinite_original_interior_flow (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {C : GeneralizedSliceCarrier.{u}}
    {base Q b t0 tau K : ℝ} (U : TopologicalSpace.Opens C.carrier)
    {V : Set C.carrier} (hV : IsOpen V) (hUV : (U : Set C.carrier) ⊆ V)
    (hne : (U : Set C.carrier).Nonempty)
    (hbase : base ∈ H.generalized.interval) (ht0 : 0 < t0)
    (htau : 0 < tau) (hb : b < -tau)
    (E : SurgeryFlowCylinder F C base Q (Icc b 0) U)
    (e : GeneralizedFlowCylinder H.generalized C base Q (Icc (-t0) 0) V)
    (hzero : ∀ (hE0 : 0 ∈ Icc b 0) (he0 : 0 ∈ Icc (-t0) 0), ∀ x ∈ U,
      E.forward 0 hE0 x = H.history.forward (base + 0 / Q)
        ((H.generalized.slice_nonempty_iff _).mp ⟨e.forward 0 he0 x⟩)
        (e.forward 0 he0 x))
    (hcurv : ∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
      |(F.connection (base + s / Q)).curvatureTensorNorm (E.forward s hs x)| ≤ K * Q) :
    ∃ A : RicciFlow 3 U (Icc (-tau) 0),
      (∀ s (hs : s ∈ Icc (-tau) 0) (x : U),
        (∀ v w : TangentSpace (𝓡 3) x,
          (A.metric s).inner x v w = E.pullbackInner s ⟨hb.le.trans hs.1, hs.2⟩ x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
        (A.connection s).scalarCurvature x =
          (F.connection (base + s / Q)).scalarCurvature
            (E.forward s ⟨hb.le.trans hs.1, hs.2⟩ x.val) / Q ∧
        (A.connection s).curvatureTensorNorm x =
          (F.connection (base + s / Q)).curvatureTensorNorm
            (E.forward s ⟨hb.le.trans hs.1, hs.2⟩ x.val) / Q) ∧
      (∀ s ∈ Icc (-tau) 0, ∀ x : U, |(A.connection s).curvatureTensorNorm x| ≤ K) ∧
      (∀ s (_hs : s ∈ Icc (-tau) 0) (hs' : s ∈ Icc (-t0) 0) (x : U),
        ∀ v w : TangentSpace (𝓡 3) x,
          (A.metric s).inner x v w = e.pullbackInner s hs' x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) := by
  have hsmall : Icc (0 : ℝ) 0 ⊆ Icc (-t0) 0 :=
    Icc_subset_Icc (neg_nonpos.mpr ht0.le) le_rfl
  let e0 := e.restrict hsmall hUV
  have hfuture : ∀ s (hs : s ∈ Icc (0 : ℝ) 0) (hs' : s ∈ Icc b 0), ∀ x ∈ U,
      E.forward s hs' x = H.history.forward (base + s / Q)
        ((H.generalized.slice_nonempty_iff _).mp ⟨e0.forward s hs x⟩)
        (e0.forward s hs x) := by
    intro s hs hs' x hx
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst s
    exact hzero hs' (hsmall hs) x hx
  obtain ⟨A, hread, hbound, _hfutureMetric⟩ :=
    limitFinite_preserved_interior_flow P H U hne hbase htau hb E e0 hfuture hcurv
  obtain ⟨x0, _hx0⟩ := hne
  have htime (s : ℝ) (hs : s ∈ Icc (-t0) 0) :
      base + s / Q ∈ H.generalized.interval :=
    (H.generalized.slice_nonempty_iff _).mp ⟨e.forward s hs x0⟩
  obtain ⟨ep, hep, hepmetric⟩ := H.cylinders_to_surgery C base Q
    (Icc (-t0) 0) V ordConnected_Icc hV htime e
  refine ⟨A, hread, hbound, ?_⟩
  intro s hs hs' x v w
  have hI : Icc s 0 ⊆ Icc b 0 := Icc_subset_Icc (hb.le.trans hs.1) le_rfl
  have hJ : Icc s 0 ⊆ Icc (-t0) 0 := Icc_subset_Icc hs'.1 le_rfl
  have hterminal : ∀ y ∈ (U : Set C.carrier) ∩ V,
      E.forward 0 (hI ⟨hs.2, le_rfl⟩) y = ep.forward 0 (hJ ⟨hs.2, le_rfl⟩) y := by
    intro y hy
    exact (hzero _ _ y hy.1).trans (hep 0 _ y hy.2).symm
  have heq := limitFinite_physical_pullback_eq E ep U.isOpen hV hs.2 hI hJ hterminal
    (show x.val ∈ (U : Set C.carrier) ∩ V from ⟨x.property, hUV x.property⟩)
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)
  exact ((hread s hs x).1 v w).trans
    (heq.trans (hepmetric s hs' x.val (hUV x.property) _ _))

end PoincareConjecture.M47
