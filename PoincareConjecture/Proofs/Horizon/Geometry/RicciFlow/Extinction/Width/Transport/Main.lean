import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.Events
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.Path
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.EventEstimate

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem horizon_m67_surgery_width_theory : M67SurgeryWidthTheory.{u} := by
  intro g₀ D W T P hcomparison hscalar K C H B A S initial hM61 hM64 hM65 hM58 hM66
  classical
  obtain ⟨cls⟩ := m67_class_path_exists H B A S initial hcomparison
  let slice := m67SliceFamily S initial cls.datum
  have hambient := m67SliceFamily_ambient_metric S initial cls.datum
  have hclass : ∀ (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1)),
      M67AlphaTransport B (P.component a).basepoint (P.component b).basepoint
        (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hJ))
        (slice a).alpha (slice b).alpha := by
    intro a b hab hJ
    change M67AlphaTransport B _ _ _
      (m67SliceFamily S initial cls.datum a).alpha
      (m67SliceFamily S initial cls.datum b).alpha
    rw [cls.slice_alpha a, cls.slice_alpha b]
    exact cls.regular_transport a b hab hJ
  let X := m67ChangingWidthPathOfSlices D W P K C H B A S hM61 hM65 hM58 hM66
    hscalar slice hambient hclass (m67ClassPathEventFamily cls)
  refine ⟨⟨X, {
    estimate := ?_
    class_coherence := ?_
    initial_metric_eq := ?_
    initial_class_eq := ?_
    identification_eq := ?_ }⟩⟩
  · apply m67_conclusion_of_event_width_calibration S X hM61 hcomparison
    intro t ht hp hd hh eta heta s hnear hbefore hafter hJ
    obtain ⟨hpre, hpost⟩ := m67ClassPathEventFamily_slices cls t ht hp hd hh eta heta
      s hnear hbefore hafter hJ
    constructor
    · change m61BasedClassWidth S.quotient
        ((m67ClassPathEventFamily cls t ht hp hd hh eta heta).transport
          s hnear hbefore hafter hJ).pre.metric (P.component s).basepoint
        ((m67ClassPathEventFamily cls t ht hp hd hh eta heta).transport
          s hnear hbefore hafter hJ).pre.alpha = _
      rw [hpre]
      rfl
    · change m61BasedClassWidth S.quotient
        ((m67ClassPathEventFamily cls t ht hp hd hh eta heta).transport
          s hnear hbefore hafter hJ).post.metric (H.event_input t ht hp).child.basepoint
        ((m67ClassPathEventFamily cls t ht hp hd hh eta heta).transport
          s hnear hbefore hafter hJ).post.alpha = _
      rw [hpost]
      exact m67EventPostSlice_based_width H t ht hp (slice t)
  · constructor
    · intro a b ha hab hb hJ
      exact hclass _ _ hab hJ
    · intro t ht hp hd hh eta heta s hnear hbefore hafter hJ
      obtain ⟨hpre, hpost⟩ := m67ClassPathEventFamily_slices cls t ht hp hd hh eta heta
        s hnear hbefore hafter hJ
      refine ⟨?_, ?_, ?_⟩
      · change HEq ((m67ClassPathEventFamily cls t ht hp hd hh eta heta).transport
          s hnear hbefore hafter hJ).pre.alpha (slice s).alpha
        rw [hpre]
      · change HEq ((m67ClassPathEventFamily cls t ht hp hd hh eta heta).transport
          s hnear hbefore hafter hJ).post.alpha (slice t).alpha
        rw [hpost]
        exact m67EventPostSlice_alpha_heq H t ht hp (slice t)
      · exact ((m67ClassPathEventFamily cls t ht hp hd hh eta heta).transport
          s hnear hbefore hafter hJ).class_transport
  · change (m67SliceFamily S initial cls.datum (m67InitialTime P)).metric = _
    rw [m67SliceFamily_initial]
    rfl
  · change (m67SliceFamily S initial cls.datum (m67InitialTime P)).alpha = _
    rw [m67SliceFamily_initial]
    rfl
  · exact m67SliceFamily_identification S initial cls.datum

end PoincareConjecture
