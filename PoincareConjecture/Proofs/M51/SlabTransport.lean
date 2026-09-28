import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

namespace SurgeryRegularSlab

variable {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier}
    {a b : ℝ}
    {S : SurgeryRegularSlab slice metric a b}
    {slice' : ℝ → GeneralizedSliceCarrier.{u}}
    {metric' : ∀ t, RiemannianMetric 3 (slice' t).carrier}
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice' a).carrier (slice a).carrier ∞}

structure PullbackData (S : SurgeryRegularSlab slice metric a b)
    (slice' : ℝ → GeneralizedSliceCarrier.{u})
    (metric' : ∀ t, RiemannianMetric 3 (slice' t).carrier)
    (initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice' a).carrier (slice a).carrier ∞) where
  flow : RicciFlow 3 (slice' a).carrier (Set.Icc a b)
  sliceMap : ∀ t : Set.Icc a b,
    Diffeomorph (𝓡 3) (𝓡 3)
      (slice t.1).carrier (slice' t.1).carrier ∞
  initial_sliceMap : ∀ x,
    sliceMap ⟨a, le_rfl, S.ordered.le⟩ (initial x) = x
  metric_pullback : ∀ (t : Set.Icc a b) (x : (slice' a).carrier)
      (v w : TangentSpace (𝓡 3) x),
    (metric' t.1).inner (initial.trans ((S.identify t).trans (sliceMap t)) x)
        (mfderiv (𝓡 3) (𝓡 3)
          (initial.trans ((S.identify t).trans (sliceMap t))) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (initial.trans ((S.identify t).trans (sliceMap t))) x w) =
      (flow.metric t.1).inner x v w

noncomputable def PullbackData.ofIsometry
    (S : SurgeryRegularSlab slice metric a b)
    (slice' : ℝ → GeneralizedSliceCarrier.{u})
    (metric' : ∀ t, RiemannianMetric 3 (slice' t).carrier)
    (initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice' a).carrier (slice a).carrier ∞)
    (sliceMap : ∀ t : Set.Icc a b,
      Diffeomorph (𝓡 3) (𝓡 3)
        (slice t.1).carrier (slice' t.1).carrier ∞)
    (initial_sliceMap : ∀ x,
      sliceMap ⟨a, le_rfl, S.ordered.le⟩ (initial x) = x)
    (slice_isometry : ∀ (t : Set.Icc a b) (y : (slice t.1).carrier)
      (v w : TangentSpace (𝓡 3) y),
      (metric' t.1).inner (sliceMap t y)
          (mfderiv (𝓡 3) (𝓡 3) (sliceMap t) y v)
          (mfderiv (𝓡 3) (𝓡 3) (sliceMap t) y w) =
        (metric t.1).inner y v w) :
    PullbackData S slice' metric' initial := by
  let e : (slice' a).carrier → (slice a).carrier := initial
  let he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := initial.isLocalDiffeomorph
  let F := S.flow.pullbackWithConnection e he
      (fun t => ((S.flow.metric t).pullbackOfLocalDiffeomorph e he).leviCivitaData)
  refine
    { flow := F
      sliceMap := sliceMap
      initial_sliceMap := initial_sliceMap
      metric_pullback := ?_ }
  intro t x v w
  let j := S.identify t
  let k := sliceMap t
  let c := initial.trans (j.trans k)
  have hc : (c : (slice' a).carrier → (slice' t.1).carrier) =
      k ∘ j ∘ e := by
    funext z
    rfl
  have he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e := initial.contMDiff
  change (metric' t.1).inner (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v)
      (mfderiv (𝓡 3) (𝓡 3) c x w) =
    (F.metric t.1).inner x v w
  rw [hc, mfderiv_comp x
    (k.contMDiff.mdifferentiable (by simp) (j (e x)))
    ((j.contMDiff.comp he').mdifferentiable (by simp) x),
    mfderiv_comp x (j.contMDiff.mdifferentiable (by simp) (e x))
      (he'.mdifferentiable (by simp) x)]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  change (metric' t.1).inner (sliceMap t (S.identify t (e x)))
      (mfderiv (𝓡 3) (𝓡 3) (sliceMap t) (S.identify t (e x))
        (mfderiv (𝓡 3) (𝓡 3) (S.identify t) (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v)))
      (mfderiv (𝓡 3) (𝓡 3) (sliceMap t) (S.identify t (e x))
        (mfderiv (𝓡 3) (𝓡 3) (S.identify t) (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x w))) =
    (F.metric t.1).inner x v w
  rw [slice_isometry t (j (e x)) _ _, S.metric_pullback t (e x) _ _]
  rfl

noncomputable def PullbackData.identify (D : PullbackData S slice' metric' initial)
    (t : Set.Icc a b) :
    Diffeomorph (𝓡 3) (𝓡 3) (slice' a).carrier (slice' t.1).carrier ∞ :=
  initial.trans ((S.identify t).trans (D.sliceMap t))

noncomputable def pullback (S : SurgeryRegularSlab slice metric a b)
    (D : PullbackData S slice' metric' initial) :
    SurgeryRegularSlab slice' metric' a b :=
  { ordered := S.ordered
    flow := D.flow
    identify := D.identify
    initial_identify := by
      intro x
      change D.sliceMap ⟨a, le_rfl, S.ordered.le⟩
        (S.identify ⟨a, le_rfl, S.ordered.le⟩ (initial x)) = x
      rw [S.initial_identify]
      exact D.initial_sliceMap x
    metric_pullback := by
      intro t x v w
      change (metric' t.1).inner
        (initial.trans ((S.identify t).trans (D.sliceMap t)) x)
        (mfderiv (𝓡 3) (𝓡 3)
          (initial.trans ((S.identify t).trans (D.sliceMap t))) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (initial.trans ((S.identify t).trans (D.sliceMap t))) x w) =
        (D.flow.metric t.1).inner x v w
      exact D.metric_pullback t x v w }

@[simp] theorem pullback_ordered
    (S : SurgeryRegularSlab slice metric a b)
    (D : PullbackData S slice' metric' initial) :
    (pullback S D).ordered = S.ordered := rfl

theorem pullback_transport
    (S : SurgeryRegularSlab slice metric a b)
    (D : PullbackData S slice' metric' initial)
    (s t : Set.Icc a b) (x : (slice s.1).carrier) :
    (pullback S D).transport s t (D.sliceMap s x) =
      D.sliceMap t (S.transport s t x) := by
  change
    (initial.trans ((S.identify t).trans (D.sliceMap t)))
        ((initial.trans ((S.identify s).trans (D.sliceMap s))).symm
          (D.sliceMap s x)) =
      D.sliceMap t
        (S.identify t ((S.identify s).symm x))
  simp only [Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.symm_trans',
    Diffeomorph.symm_apply_apply, Diffeomorph.apply_symm_apply]

theorem pullback_transport_symm
    (S : SurgeryRegularSlab slice metric a b)
    (D : PullbackData S slice' metric' initial)
    (s t : Set.Icc a b) (y : (slice' s.1).carrier) :
    (pullback S D).transport s t y =
      D.sliceMap t (S.transport s t ((D.sliceMap s).symm y)) := by
  simpa only [Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.symm_trans',
    Diffeomorph.symm_apply_apply, Diffeomorph.apply_symm_apply,
    SurgeryRegularSlab.transport] using
    (pullback_transport S D s t ((D.sliceMap s).symm y))

end SurgeryRegularSlab

end PoincareConjecture
