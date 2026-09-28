import PoincareConjecture.Proofs.M48.ExtensionEvents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SurgeryFlowExtension

noncomputable def refl (F : SurgeryFlowData.{u}) : SurgeryFlowExtension F where
  extended := F
  old_times := Subset.rfl
  standard_initial_eq := rfl
  local_constants_eq := rfl
  parameters_eq := rfl
  identify := fun _ _ => Diffeomorph.refl (𝓡 3) _ ∞
  metric_pullback := by
    intro t ht x v w
    change (F.metric t).inner (id x)
      (mfderiv (𝓡 3) (𝓡 3) (id : (F.slice t).carrier → (F.slice t).carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (id : (F.slice t).carrier → (F.slice t).carrier) x w) = _
    simp only [mfderiv_id]
    rfl
  old_surgery_times := fun _ _ => Iff.rfl
  ordinary_compatibility := by
    intro a b hab hJ hfree hJ' hfree' s t x
    change (F.regular_slabs a b hab hJ' hfree').transport s t x =
      (F.regular_slabs a b hab hJ hfree).transport s t x
    exact F.slab_transport_coherent a b a b hab hJ hfree hab hJ' hfree'
      s t s.2 t.2 s.2 t.2 x
  old_event_reference := by
    intro T hT hT' _ _
    rfl
  old_retained_post := by
    intro T hT hT' _ _
    change (fun x : (F.slice T).carrier => x) '' (F.event T hT).retained_post = _
    exact Set.image_id _
  old_retained_pre := by
    intro T hT hT' _ _ t ht ht'
    change (fun x =>
      ((F.event T hT').pre_identify ⟨t.1, ht'⟩).symm
        ((F.event T hT).pre_identify t x)) '' (F.event T hT).retained_pre = _
    cases Subsingleton.elim hT' hT
    rw [show (F.event T hT).pre_identify ⟨t.1, ht'⟩ =
        (F.event T hT).pre_identify t by congr 1]
    simp
  old_retention := by
    intro T hT hT' _ _ t ht ht' x hx
    cases Subsingleton.elim hT' hT
    simp
  old_vanishing_reference := by
    intro T hT hT' _ _
    rfl

noncomputable def trans {F : SurgeryFlowData.{u}}
    (E : SurgeryFlowExtension F)
    (D : SurgeryFlowExtension E.extended) : SurgeryFlowExtension F where
  extended := D.extended
  old_times := fun t ht => D.old_times (E.old_times ht)
  standard_initial_eq := D.standard_initial_eq.trans E.standard_initial_eq
  local_constants_eq := D.local_constants_eq.trans E.local_constants_eq
  parameters_eq := D.parameters_eq.trans E.parameters_eq
  identify := fun t ht =>
    (E.identify t ht).trans (D.identify t (E.old_times ht))
  metric_pullback := by
    intro t ht x v w
    let e := E.identify t ht
    let d := D.identify t (E.old_times ht)
    change (D.extended.metric t).inner (d (e x))
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ e) x v)
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ e) x w) = _
    rw [mfderiv_comp x (d.contMDiff.mdifferentiable (by simp) (e x))
      (e.contMDiff.mdifferentiable (by simp) x)]
    change (D.extended.metric t).inner (d (e x))
      (mfderiv (𝓡 3) (𝓡 3) d (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v))
      (mfderiv (𝓡 3) (𝓡 3) d (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x w)) = _
    rw [D.metric_pullback]
    exact E.metric_pullback t ht x v w
  old_surgery_times := by
    intro t ht
    exact (D.old_surgery_times t (E.old_times ht)).trans (E.old_surgery_times t ht)
  ordinary_compatibility := by
    intro a b hab hJ hfree hJ' hfree' s t x
    have hJE : Icc a b ⊆ E.extended.time_domain := hJ.trans E.old_times
    have hfreeE : Disjoint E.extended.surgery_times (Ioc a b) := by
      rw [Set.disjoint_left]
      intro z hzE hzI
      exact Set.disjoint_left.mp hfree'
        ((D.old_surgery_times z (hJE ⟨hzI.1.le, hzI.2⟩)).mpr hzE) hzI
    have hD := D.ordinary_compatibility a b hab hJE hfreeE hJ' hfree' s t
      (E.identify s (hJ s.2) x)
    have hE := E.ordinary_compatibility a b hab hJ hfree hJE hfreeE s t x
    rw [hE] at hD
    exact hD
  old_event_reference := by
    intro T hT hF hG hT'
    haveI : Nonempty (E.extended.slice T).carrier :=
      Nonempty.map (E.identify T (F.surgery_times_subset hT)) hF
    have hTmid : T ∈ E.extended.surgery_times :=
      (D.old_surgery_times T (E.old_times (F.surgery_times_subset hT))).mp hT'
    have hD := D.old_event_reference T hTmid hT'
    have hE := E.old_event_reference T hT hTmid
    exact hD.trans hE
  old_retained_post := by
    intro T hT hT' hF hG
    haveI : Nonempty (E.extended.slice T).carrier :=
      Nonempty.map (E.identify T (F.surgery_times_subset hT)) hF
    have hTmid : T ∈ E.extended.surgery_times :=
      (D.old_surgery_times T (E.old_times (F.surgery_times_subset hT))).mp hT'
    have hE := E.old_retained_post T hT hTmid
    have hD := D.old_retained_post T hTmid hT'
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change D.identify T (E.extended.surgery_times_subset hTmid)
        (E.identify T (F.surgery_times_subset hT) x) ∈ _
      have hy : E.identify T (F.surgery_times_subset hT) x ∈
          (E.extended.event T hTmid).retained_post := by
        rw [← hE]
        exact ⟨x, hx, rfl⟩
      rw [← hD]
      exact ⟨_, hy, rfl⟩
    · intro hy
      rw [← hD] at hy
      rcases hy with ⟨z, hz, rfl⟩
      rw [← hE] at hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  old_retained_pre := by
    intro T hT hT' hF hG t ht ht'
    haveI : Nonempty (E.extended.slice T).carrier :=
      Nonempty.map (E.identify T (F.surgery_times_subset hT)) hF
    have hTmid : T ∈ E.extended.surgery_times :=
      (D.old_surgery_times T (E.old_times (F.surgery_times_subset hT))).mp hT'
    have hEref := E.old_event_reference T hT hTmid
    have htMidMem : t.1 ∈ Set.Ico (E.extended.event T hTmid).tMinus T := by
      simpa only [hEref] using t.2
    let tMid : Set.Ico (E.extended.event T hTmid).tMinus T :=
      ⟨t.1, htMidMem⟩
    have hE := E.old_retained_pre T hT hTmid t ht htMidMem
    have hD := D.old_retained_pre T hTmid hT' tMid
      (E.old_times ht) ht'
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let z := ((E.extended.event T hTmid).pre_identify tMid).symm
        (E.identify t.1 ht ((F.event T hT).pre_identify t x))
      have hz : z ∈ (E.extended.event T hTmid).retained_pre := by
        rw [← hE]
        exact ⟨x, hx, rfl⟩
      rw [← hD]
      refine ⟨z, hz, ?_⟩
      simp [z, tMid, Diffeomorph.coe_trans, Function.comp_apply]
    · intro hy
      rw [← hD] at hy
      rcases hy with ⟨z, hz, hzy⟩
      rw [← hE] at hz
      rcases hz with ⟨x, hx, hzx⟩
      refine ⟨x, hx, ?_⟩
      have hcomp :
          (fun q => ((D.extended.event T hT').pre_identify ⟨tMid.1, ht'⟩).symm
            ((D.identify tMid.1 (E.old_times ht))
              ((E.extended.event T hTmid).pre_identify tMid q)))
              (((E.extended.event T hTmid).pre_identify ⟨t.1, htMidMem⟩).symm
                (E.identify t.1 ht ((F.event T hT).pre_identify t x))) = y := by
        exact (congrArg (fun q =>
          ((D.extended.event T hT').pre_identify ⟨tMid.1, ht'⟩).symm
            ((D.identify tMid.1 (E.old_times ht))
              ((E.extended.event T hTmid).pre_identify tMid q))) hzx).trans hzy
      simpa [tMid] using hcomp
  old_retention := by
    intro T hT hT' hF hG t ht ht' x hx
    letI : Nonempty (E.extended.slice T).carrier :=
      Nonempty.map (E.identify T (F.surgery_times_subset hT)) hF
    have hTmid : T ∈ E.extended.surgery_times :=
      (D.old_surgery_times T (E.old_times (F.surgery_times_subset hT))).mp hT'
    have hEref := E.old_event_reference T hT hTmid
    have htMidMem : t.1 ∈ Set.Ico (E.extended.event T hTmid).tMinus T := by
      simpa only [hEref] using t.2
    let tMid : Set.Ico (E.extended.event T hTmid).tMinus T :=
      ⟨t.1, htMidMem⟩
    let z := ((E.extended.event T hTmid).pre_identify tMid).symm
      (E.identify t.1 ht ((F.event T hT).pre_identify t x))
    have hEpre := E.old_retained_pre T hT hTmid t ht htMidMem
    have hz : z ∈ (E.extended.event T hTmid).retained_pre := by
      rw [← hEpre]
      exact ⟨x, hx, rfl⟩
    have hEret := E.old_retention T hT hTmid t ht htMidMem x hx
    have hDret := D.old_retention T hTmid hT' tMid
      (E.old_times ht) ht' z hz
    rw [Diffeomorph.coe_trans]
    change D.identify T (E.extended.surgery_times_subset hTmid)
        (E.identify T (F.surgery_times_subset hT)
          ((F.event T hT).retention.map x)) =
      (D.extended.event T hT').retention.map
        (((D.extended.event T hT').pre_identify ⟨t.1, ht'⟩).symm
          ((D.identify t.1 (E.old_times ht))
            (E.identify t.1 ht ((F.event T hT).pre_identify t x))))
    rw [hEret, hDret]
    simp [z, tMid]
  old_vanishing_reference := by
    intro T hT hF hG hT'
    haveI : IsEmpty (E.extended.slice T).carrier :=
      ⟨fun y => isEmptyElim ((E.identify T (F.surgery_times_subset hT)).symm y)⟩
    have hTmid : T ∈ E.extended.surgery_times :=
      (D.old_surgery_times T (E.old_times (F.surgery_times_subset hT))).mp hT'
    have hD := D.old_vanishing_reference T hTmid hT'
    have hE := E.old_vanishing_reference T hT hTmid
    exact hD.trans hE

end SurgeryFlowExtension

end PoincareConjecture
