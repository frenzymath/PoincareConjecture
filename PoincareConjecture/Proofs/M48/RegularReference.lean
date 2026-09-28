import PoincareConjecture.Proofs.M48.ReferenceSlab

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

structure M48RegularReferenceData {F : SurgeryFlowData.{u}} {T : ℝ}
    (L : RepairedPreterminalSlab F T) (H : M33RegularHistoryData L.regularHistoryWindow) where
  reference : SingularTimeReference H.generalized T (F.slice L.start).carrier
  start_inside : L.start < reference.tMinus
  metric_eq : reference.flow.metric = L.flow.metric
  connection_eq : HEq reference.flow.connection L.flow.connection
  history_eq : ∀ t ht x,
    H.history.forward t (reference.window_subset ht) (reference.forward t ht x) =
      L.identify ⟨t, start_inside.le.trans ht.1, ht.2⟩ x

namespace M48Predecessors

variable (P : M48Predecessors.{u}) {F : SurgeryFlowData.{u}} {T : ℝ}
  {L : RepairedPreterminalSlab F T} (R : M48RegularSpacetimeData L)

include P

theorem regular_reference (a : ℝ) (ha : L.start < a) (haT : a < T) :
    ∃ D : M48RegularReferenceData L R.history, D.reference.tMinus = a := by
  let H := R.history
  let J := Ico a T
  have htime (t : ℝ) (ht : t ∈ J) : t ∈ H.generalized.interval := by
    rw [H.interval_eq]
    exact ⟨(F.time_domain_nonnegative L.start_mem).trans (ha.le.trans ht.1), ht.2⟩
  let f (t : ℝ) (ht : t ∈ J) : Diffeomorph (𝓡 3) (𝓡 3)
      (F.slice L.start).carrier (H.generalized.slice t).carrier ∞ :=
    (L.identify ⟨t, L.reference_window_subset ha ht⟩).trans
      (H.regularDiffeomorph t (htime t ht) (L.reference_regular ha t ht)).symm
  have hcommute (t : ℝ) (ht : t ∈ J) (x : (F.slice L.start).carrier) :
      H.history.forward t (htime t ht) (f t ht x) =
        L.identify ⟨t, L.reference_window_subset ha ht⟩ x := by
    exact (H.regularDiffeomorph t (htime t ht) (L.reference_regular ha t ht)).apply_symm_apply _
  let e := L.referenceCylinder ha
  have hclock (t : ℝ) (ht : t ∈ J) : 0 + t / 1 ∈ H.generalized.interval := by
    simpa only [div_one, zero_add] using htime t ht
  obtain ⟨d, hd, hmetric⟩ := H.cylinders_from_surgery (F.slice L.start) 0 1 J univ
    isOpen_univ hclock e (by
      intro s hs
      have hsreg : 0 + s / 1 ∉ F.surgery_times := by
        simpa only [div_one, zero_add] using L.reference_regular ha s hs
      rw [m33RegularRegion_of_regular F _ hsreg]
      exact subset_univ _)
  have heq (t : ℝ) (ht : t ∈ J) : d.forward t ht =
      ⇑(f (0 + t / 1) (by simpa only [div_one, zero_add] using ht)) := by
    funext x
    apply (H.history.forward_openEmbedding (0 + t / 1) (hclock t ht)).injective
    exact (hd t ht x (mem_univ x)).trans
      (hcommute _ (by simpa only [div_one, zero_add] using ht) x).symm
  have hpoint : (fun p : J × (F.slice L.start).carrier =>
      (⟨p.1.1, f p.1.1 p.1.2 p.2⟩ : H.generalized.point)) =
      (fun p : J × (univ : Set (F.slice L.start).carrier) =>
        d.pointMap p.1.1 p.1.2 p.2.1) ∘
        (Homeomorph.prodCongr (Homeomorph.refl J)
          (Homeomorph.Set.univ (F.slice L.start).carrier).symm) := by
    funext p
    dsimp [GeneralizedFlowCylinder.pointMap]
    rw [heq]
    exact congrArg (fun s : J => (⟨s.1, f s.1 s.2 p.2⟩ : H.generalized.point))
      (show p.1 = (⟨0 + p.1.1 / 1, by simpa only [div_one, zero_add] using p.1.2⟩ : J)
        from Subtype.ext (by simp only [div_one, zero_add]))
  have hmetric' (t : ℝ) (ht : t ∈ J) (x : (F.slice L.start).carrier)
      (v w : TangentSpace (𝓡 3) x) :
      (H.generalized.metric t).inner (f t ht x)
        (mfderiv (𝓡 3) (𝓡 3) (f t ht) x v)
        (mfderiv (𝓡 3) (𝓡 3) (f t ht) x w) = (L.flow.metric t).inner x v w := by
    have h := hmetric t ht x (mem_univ x) v w
    dsimp only [GeneralizedFlowCylinder.pullbackInner, SurgeryFlowCylinder.pullbackInner] at h
    rw [heq] at h
    simp only [e, RepairedPreterminalSlab.referenceCylinder, one_mul] at h
    have h' := h.trans (L.metric_pullback ⟨0 + t / 1, by
      simpa only [div_one, zero_add] using L.reference_window_subset ha ht⟩ x v w)
    have hvalue := congrArg (fun s : J =>
      (H.generalized.metric s.1).inner (f s.1 s.2 x)
        (mfderiv (𝓡 3) (𝓡 3) (f s.1 s.2) x v)
        (mfderiv (𝓡 3) (𝓡 3) (f s.1 s.2) x w))
      (show (⟨t, ht⟩ : J) = ⟨0 + t / 1, by simpa using ht⟩ from
        Subtype.ext (by simp))
    exact hvalue.trans (h'.trans (by simp only [div_one, zero_add]))
  have hscalar (t : ℝ) (ht : t ∈ J) (x : (F.slice L.start).carrier) :
      (H.generalized.connection t).scalarCurvature (f t ht x) =
        (L.flow.connection t).scalarCurvature x := by
    rw [← H.scalar_pullback t (htime t ht), hcommute t ht x]
    have hhom : MetricHomothety (L.flow.metric t) (F.metric t)
        (L.identify ⟨t, L.reference_window_subset ha ht⟩) 1 := by
      intro y v w
      simpa only [one_mul] using
        L.metric_pullback ⟨t, L.reference_window_subset ha ht⟩ y v w
    have hc := P.m13.metric_homothety _ _ (L.flow.metric t) (F.metric t)
      (L.identify ⟨t, L.reference_window_subset ha ht⟩) 1 zero_lt_one hhom
    simpa only [div_one] using hc.scalar_eq (L.flow.connection t) (F.connection t) x
  let reference : SingularTimeReference H.generalized T (F.slice L.start).carrier := {
    tMinus := a
    tMinus_mem := htime a ⟨le_rfl, haT⟩
    tMinus_lt := haT
    window_subset := fun t ht => htime t ht
    flow := L.referenceFlow ha haT
    forward := fun t ht => f t ht
    inverse := fun t ht => (f t ht).symm
    forward_openEmbedding := fun t ht => (f t ht).toHomeomorph.isOpenEmbedding
    forward_smooth := fun t ht => (f t ht).contMDiff
    inverse_smooth := fun t ht => (f t ht).symm.contMDiff
    forward_surjective := fun t ht => (f t ht).surjective
    left_inverse := fun t ht => (f t ht).left_inv
    right_inverse := fun t ht => (f t ht).right_inv
    metric_pullback := hmetric'
    scalar_pullback := hscalar
    spacetime_forward := fun p => ⟨p.1.1, f p.1.1 p.1.2 p.2⟩
    spacetime_time := fun _ => rfl
    spacetime_spatial := fun _ => HEq.rfl
    spacetime_embedding := by
      rw [hpoint]
      exact d.embedding.comp (Homeomorph.prodCongr (Homeomorph.refl J)
        (Homeomorph.Set.univ (F.slice L.start).carrier).symm).isEmbedding
    spacetime_image := by
      ext p
      constructor
      · rintro ⟨q, rfl⟩
        exact q.1.2
      · intro hp
        exact ⟨(⟨p.1, hp⟩, (f p.1 hp).symm p.2), by simp⟩
    vertical_compatibility := by
      intro t ht x
      obtain ⟨b, y, δ, hδ, hv⟩ := d.vertical_compatibility t ht x (mem_univ x)
      refine ⟨b, y, δ, hδ, ?_⟩
      intro s hs hst
      obtain ⟨hb, hforward⟩ := hv s hs hst
      rw [heq] at hforward
      have h' : ∃ hb : 0 + s / 1 ∈ (H.generalized.box b).interval,
          f (0 + s / 1) (by simpa only [div_one, zero_add] using hs) x =
            (H.generalized.box b).forward (0 + s / 1) hb y := ⟨hb, hforward⟩
      have htimeEq : (⟨0 + s / 1, by
          simpa only [div_one, zero_add] using (show s ∈ J from hs)⟩ : J) = ⟨s, hs⟩ :=
        Subtype.ext (by simp)
      exact (congrArg (fun q : J => ∃ hb : q.1 ∈ (H.generalized.box b).interval,
        f q.1 q.2 x = (H.generalized.box b).forward q.1 hb y) htimeEq).mp h' }
  exact ⟨⟨reference, ha, rfl, HEq.rfl, hcommute⟩, rfl⟩

theorem regular_reference_exists : Nonempty (M48RegularReferenceData L R.history) := by
  obtain ⟨a, ha, haT⟩ := exists_between L.start_lt
  obtain ⟨D, _⟩ := P.regular_reference R a ha haT
  exact ⟨D⟩

end M48Predecessors

end PoincareConjecture
