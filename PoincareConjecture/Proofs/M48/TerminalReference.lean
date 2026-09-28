import PoincareConjecture.Proofs.M48.SingularInput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

private theorem scalar_family_eq (M : GeneralizedSliceCarrier.{u})
    {g h : ℝ → RiemannianMetric 3 M.carrier}
    (D : ∀ t, LeviCivitaData (g t)) (E : ∀ t, LeviCivitaData (h t))
    (hg : g = h) (hD : HEq D E) :
    (fun t x => (D t).scalarCurvature x) = fun t x => (E t).scalarCurvature x := by
  cases hg
  cases hD
  rfl

namespace M48RegularReferenceData

variable {F : SurgeryFlowData.{u}} {T : ℝ}
  {L : RepairedPreterminalSlab F T} {R : M33RegularHistoryData L.regularHistoryWindow}
  (D : M48RegularReferenceData L R)

theorem scalar_eq (t : ℝ) (x : (F.slice L.start).carrier) :
    (D.reference.flow.connection t).scalarCurvature x =
      (L.flow.connection t).scalarCurvature x :=
  congrFun (congrFun (scalar_family_eq (F.slice L.start)
    D.reference.flow.connection L.flow.connection D.metric_eq D.connection_eq) t) x

noncomputable def identify (t : Ico D.reference.tMinus T) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t.1).carrier (F.slice L.start).carrier ∞ :=
  (L.identify ⟨t.1, D.start_inside.le.trans t.2.1, t.2.2⟩).symm

theorem identify_slab (t : Ico D.reference.tMinus T) (x : (F.slice L.start).carrier) :
    D.identify t (L.identify ⟨t.1, D.start_inside.le.trans t.2.1, t.2.2⟩ x) = x :=
  (L.identify _).symm_apply_apply x

theorem history_identify (t : Ico D.reference.tMinus T) (x : (F.slice L.start).carrier) :
    R.history.forward t.1 (D.reference.window_subset t.2)
      (D.reference.forward t.1 t.2 x) = (D.identify t).symm x :=
  D.history_eq t.1 t.2 x

theorem metric_pullback (t : Ico D.reference.tMinus T)
    (x : (F.slice L.start).carrier) (v w : TangentSpace (𝓡 3) x) :
    let s : Ico L.start T := ⟨t.1, D.start_inside.le.trans t.2.1, t.2.2⟩
    (D.reference.flow.metric t.1).inner (D.identify t (L.identify s x))
      (mfderiv (𝓡 3) (𝓡 3) (D.identify t) (L.identify s x)
        (mfderiv (𝓡 3) (𝓡 3) (L.identify s) x v))
      (mfderiv (𝓡 3) (𝓡 3) (D.identify t) (L.identify s x)
        (mfderiv (𝓡 3) (𝓡 3) (L.identify s) x w)) =
      (L.flow.metric t.1).inner x v w := by
  let e := L.identify ⟨t.1, D.start_inside.le.trans t.2.1, t.2.2⟩
  have hcomp : e.symm ∘ e = id := by funext y; exact e.symm_apply_apply y
  have hd : (mfderiv (𝓡 3) (𝓡 3) e.symm (e x)).comp
      (mfderiv (𝓡 3) (𝓡 3) e x) = ContinuousLinearMap.id ℝ _ := by
    rw [← mfderiv_comp x (e.symm.contMDiff.mdifferentiable (by simp) _)
      (e.contMDiff.mdifferentiable (by simp) _), hcomp, mfderiv_id]
  have hv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x z) = z :=
    congrArg (fun f => f z) hd
  change (D.reference.flow.metric t.1).inner (e.symm (e x))
    (mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v))
    (mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w)) = _
  rw [hv, hv, e.symm_apply_apply, congrFun D.metric_eq t.1]

theorem scalar_pullback (t : Ico D.reference.tMinus T) (x : (F.slice L.start).carrier) :
    let s : Ico L.start T := ⟨t.1, D.start_inside.le.trans t.2.1, t.2.2⟩
    (D.reference.flow.connection t.1).scalarCurvature (D.identify t (L.identify s x)) =
      (L.flow.connection t.1).scalarCurvature x := by
  dsimp only
  rw [D.identify_slab]
  exact D.scalar_eq _ _

theorem transport_compatibility (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (habs : Disjoint F.surgery_times (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico D.reference.tMinus T) (ht' : t ∈ Ico D.reference.tMinus T)
    (x : (F.slice s).carrier) :
    D.identify ⟨t, ht'⟩
        ((F.regular_slabs a b hab hJ habs).transport ⟨s, hs⟩ ⟨t, ht⟩ x) =
      D.identify ⟨s, hs'⟩ x := by
  let s' : Ico L.start T := ⟨s, D.start_inside.le.trans hs'.1, hs'.2⟩
  let t' : Ico L.start T := ⟨t, D.start_inside.le.trans ht'.1, ht'.2⟩
  have h := L.transport_compatibility a b hab hJ habs s t hs ht s'.2 t'.2
    ((L.identify s').symm x)
  simpa only [s', t', identify, Diffeomorph.apply_symm_apply,
    Diffeomorph.symm_apply_apply] using
    congrArg (L.identify t').symm h

end M48RegularReferenceData

end PoincareConjecture
