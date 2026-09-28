import PoincareConjecture.Proofs.M51.StageSequence
import PoincareConjecture.Proofs.M48.ExtensionMetric










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M51.ComposedExtension

variable {F G : SurgeryFlowData.{u}}
  (D : SurgeryFlowExtension F) (hD : D.extended = G)

include D hD


theorem standardInitialTo : G.standard_initial = F.standard_initial := by
  subst G
  exact D.standard_initial_eq


theorem localConstantsTo : G.local_constants = F.local_constants := by
  subst G
  exact D.local_constants_eq


theorem parametersTo : G.parameters = F.parameters := by
  subst G
  exact D.parameters_eq


theorem oldSurgeryTimeTo (t : ℝ) (ht : t ∈ F.time_domain) :
    t ∈ G.surgery_times ↔ t ∈ F.surgery_times := by
  subst G
  exact D.old_surgery_times t ht


theorem identifyTo_metric_pullback
    (t : ℝ) (ht : t ∈ F.time_domain) (x : (F.slice t).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (G.metric t).inner (identifyTo D hD t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (identifyTo D hD t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identifyTo D hD t ht) x w) =
        (F.metric t).inner x v w := by
  subst G
  exact D.metric_pullback t ht x v w


theorem identifyTo_metric_homothety (t : ℝ) (ht : t ∈ F.time_domain) :
    MetricHomothety (F.metric t) (G.metric t) (identifyTo D hD t ht) 1 := by
  subst G
  exact D.metric_homothety t ht


theorem identifyTo_metric_homothety_symm (t : ℝ) (ht : t ∈ F.time_domain) :
    MetricHomothety (G.metric t) (F.metric t) (identifyTo D hD t ht).symm 1 := by
  subst G
  exact D.metric_homothety_symm t ht


theorem ordinaryCompatibilityTo
    (a b : ℝ) (hab : a < b)
    (hJ : Set.Icc a b ⊆ F.time_domain)
    (habs : Disjoint F.surgery_times (Set.Ioc a b))
    (hJ' : Set.Icc a b ⊆ G.time_domain)
    (habs' : Disjoint G.surgery_times (Set.Ioc a b))
    (s t : Set.Icc a b) (x : (F.slice s.1).carrier) :
    (G.regular_slabs a b hab hJ' habs').transport s t
      (identifyTo D hD s.1 (hJ s.2) x) =
        identifyTo D hD t.1 (hJ t.2)
          ((F.regular_slabs a b hab hJ habs).transport s t x) := by
  subst G
  exact D.ordinary_compatibility a b hab hJ habs hJ' habs' s t x


theorem oldEventReferenceTo
    (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty (G.slice T).carrier]
    (hT' : T ∈ G.surgery_times) :
    (G.event T hT').tMinus = (F.event T hT).tMinus := by
  subst G
  exact D.old_event_reference T hT hT'


theorem oldRetainedPostTo
    (T : ℝ) (hT : T ∈ F.surgery_times) (hT' : T ∈ G.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty (G.slice T).carrier] :
    identifyTo D hD T (F.surgery_times_subset hT) ''
      (F.event T hT).retained_post = (G.event T hT').retained_post := by
  subst G
  exact D.old_retained_post T hT hT'


theorem oldRetainedPreTo
    (T : ℝ) (hT : T ∈ F.surgery_times) (hT' : T ∈ G.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty (G.slice T).carrier]
    (t : Set.Ico (F.event T hT).tMinus T)
    (ht : t.1 ∈ F.time_domain)
    (ht' : t.1 ∈ Set.Ico (G.event T hT').tMinus T) :
    (fun x => ((G.event T hT').pre_identify ⟨t.1, ht'⟩).symm
      (identifyTo D hD t.1 ht ((F.event T hT).pre_identify t x))) ''
        (F.event T hT).retained_pre = (G.event T hT').retained_pre := by
  subst G
  exact D.old_retained_pre T hT hT' t ht ht'


theorem oldRetentionTo
    (T : ℝ) (hT : T ∈ F.surgery_times) (hT' : T ∈ G.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty (G.slice T).carrier]
    (t : Set.Ico (F.event T hT).tMinus T)
    (ht : t.1 ∈ F.time_domain)
    (ht' : t.1 ∈ Set.Ico (G.event T hT').tMinus T)
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hx : x ∈ (F.event T hT).retained_pre) :
    identifyTo D hD T (F.surgery_times_subset hT)
      ((F.event T hT).retention.map x) =
        (G.event T hT').retention.map
          (((G.event T hT').pre_identify ⟨t.1, ht'⟩).symm
            (identifyTo D hD t.1 ht ((F.event T hT).pre_identify t x))) := by
  subst G
  exact D.old_retention T hT hT' t ht ht' x hx


theorem oldVanishingReferenceTo
    (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] [IsEmpty (G.slice T).carrier]
    (hT' : T ∈ G.surgery_times) :
    (G.vanishing_event T hT').tMinus =
      (F.vanishing_event T hT).tMinus := by
  subst G
  exact D.old_vanishing_reference T hT hT'

end PoincareConjecture.M51.ComposedExtension
