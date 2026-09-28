import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.SurgeryEventRebuild

abbrev SliceMetric := (S : GeneralizedSliceCarrier.{u}) × RiemannianMetric 3 S.carrier

theorem sliceMetric_eq {A B : SliceMetric.{u}} (hS : A.1 = B.1)
    (hg : HEq A.2 B.2) : A = B := Sigma.ext hS hg

def relabel {C : SliceMetric.{u} → Sort v} {s t : SliceMetric.{u}}
    (h : s = t) (x : C s) : C t := h ▸ x

theorem relabel_heq {C : SliceMetric.{u} → Sort v} {s t : SliceMetric.{u}}
    (h : s = t) (x : C s) : HEq (relabel h x) x := by
  subst t
  rfl

noncomputable def identify (s t : SliceMetric.{u}) (h : s = t) :
    Diffeomorph (𝓡 3) (𝓡 3) s.1.carrier t.1.carrier ∞ := by
  subst t
  exact Diffeomorph.refl (𝓡 3) s.1.carrier ∞

theorem identify_apply_heq {s t : SliceMetric.{u}} (h : s = t) (x : s.1.carrier) :
    HEq (identify s t h x) x := by
  subst t
  rfl

theorem relabel_set_image {s t : SliceMetric.{u}} (h : s = t)
    (U : Set s.1.carrier) :
    identify s t h '' U = relabel (C := fun r => Set r.1.carrier) h U := by
  subst t
  exact Set.image_id _

def regionSource {s t : SliceMetric.{u}} (h : s = t)
    (B : GeneralizedSliceCarrier.{u}) (U : Set s.1.carrier) (V : Set B.carrier)
    (e : SurgeryRegionEquivalence s.1 B U V) :
    SurgeryRegionEquivalence t.1 B
      (relabel (C := fun r => Set r.1.carrier) h U) V := by
  subst t
  exact e

theorem regionSource_map {s t : SliceMetric.{u}} (h : s = t)
    (B : GeneralizedSliceCarrier.{u}) (U : Set s.1.carrier) (V : Set B.carrier)
    (e : SurgeryRegionEquivalence s.1 B U V) (x : s.1.carrier) :
    (regionSource h B U V e).map (identify s t h x) = e.map x := by
  subst t
  rfl

def region {s s' t t' : SliceMetric.{u}} (hs : s = s') (ht : t = t')
    (U : Set s.1.carrier) (V : Set t.1.carrier)
    (e : SurgeryRegionEquivalence s.1 t.1 U V) :
    SurgeryRegionEquivalence s'.1 t'.1
      (relabel (C := fun r => Set r.1.carrier) hs U)
      (relabel (C := fun r => Set r.1.carrier) ht V) := by
  subst s'
  subst t'
  exact e

theorem region_map {s s' t t' : SliceMetric.{u}} (hs : s = s') (ht : t = t')
    (U : Set s.1.carrier) (V : Set t.1.carrier)
    (e : SurgeryRegionEquivalence s.1 t.1 U V) (x : s.1.carrier) :
    (region hs ht U V e).map (identify s s' hs x) =
      identify t t' ht (e.map x) := by
  subst s'
  subst t'
  rfl

noncomputable def diffeomorph {s s' t t' : SliceMetric.{u}}
    (hs : s = s') (ht : t = t')
    (f : Diffeomorph (𝓡 3) (𝓡 3) s.1.carrier t.1.carrier ∞) :
    Diffeomorph (𝓡 3) (𝓡 3) s'.1.carrier t'.1.carrier ∞ := by
  subst s'
  subst t'
  exact f

theorem diffeomorph_apply {s s' t t' : SliceMetric.{u}}
    (hs : s = s') (ht : t = t')
    (f : Diffeomorph (𝓡 3) (𝓡 3) s.1.carrier t.1.carrier ∞) (x : s.1.carrier) :
    diffeomorph hs ht f (identify s s' hs x) = identify t t' ht (f x) := by
  subst s'
  subst t'
  rfl

noncomputable def flow {s t : SliceMetric.{u}} (h : s = t) {J : Set ℝ}
    (B : RicciFlow 3 s.1.carrier J) : RicciFlow 3 t.1.carrier J := h ▸ B

theorem flow_heq {s t : SliceMetric.{u}} (h : s = t) {J : Set ℝ}
    (B : RicciFlow 3 s.1.carrier J) : HEq (flow h B) B := by
  subst t
  rfl

theorem diffeomorph_flow_metric_pullback {s s' t t' : SliceMetric.{u}}
    (hs : s = s') (ht : t = t') {J : Set ℝ}
    (B : RicciFlow 3 s.1.carrier J) (r : ℝ)
    (f : Diffeomorph (𝓡 3) (𝓡 3) s.1.carrier t.1.carrier ∞)
    (h : ∀ x v w, t.2.inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
        (B.metric r).inner x v w) :
    ∀ x v w, t'.2.inner (diffeomorph hs ht f x)
      (mfderiv (𝓡 3) (𝓡 3) (diffeomorph hs ht f) x v)
      (mfderiv (𝓡 3) (𝓡 3) (diffeomorph hs ht f) x w) =
        ((flow hs B).metric r).inner x v w := by
  subst s'
  subst t'
  exact h

end PoincareConjecture.SurgeryEventRebuild
