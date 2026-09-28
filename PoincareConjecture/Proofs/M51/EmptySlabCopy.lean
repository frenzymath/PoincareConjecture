import PoincareConjecture.Proofs.M51.EmptyEventCopy

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SurgeryRegularSlab

variable {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {p q : ℝ}

noncomputable def m51_reindexPast (S : SurgeryRegularSlab slice metric p q)
    (tau : ℝ → ℝ) (hTau : ∀ t ≤ q, tau t = t) :
    SurgeryRegularSlab (fun t => slice (tau t)) (fun t => metric (tau t)) p q := by
  have hp := hTau p S.ordered.le
  refine {
    ordered := S.ordered
    flow := M51EventCopy.flow slice hp.symm S.flow
    identify := fun t => M51EventCopy.diffeomorph slice hp.symm
      (hTau t.1 t.2.2).symm (S.identify t)
    initial_identify := ?_
    metric_pullback := ?_ }
  · intro x
    obtain ⟨y, rfl⟩ := (M51EventCopy.timeEquivalence slice p (tau p) hp.symm).surjective x
    exact (M51EventCopy.diffeomorph_apply slice hp.symm hp.symm
      (S.identify ⟨p, le_rfl, S.ordered.le⟩) y).trans
        (congrArg (M51EventCopy.timeEquivalence slice p (tau p) hp.symm)
          (S.initial_identify y))
  · intro t
    exact M51EventCopy.diffeomorph_flow_metric_pullback slice metric hp.symm
      (hTau t.1 t.2.2).symm S.flow t.1 (S.identify t) (S.metric_pullback t)

theorem m51_reindexPast_transport_heq (S : SurgeryRegularSlab slice metric p q)
    (tau : ℝ → ℝ) (hTau : ∀ t ≤ q, tau t = t) (s t : Set.Icc p q)
    {x : (slice s.1).carrier} {y : (slice (tau s.1)).carrier} (hy : HEq y x) :
    HEq ((S.m51_reindexPast tau hTau).transport s t y) (S.transport s t x) := by
  let S' := S.m51_reindexPast tau hTau
  let c := M51EventCopy.identify slice tau p (hTau p S.ordered.le)
  have hmap (r : Set.Icc p q) (z : (slice p).carrier) :
      S'.identify r (c z) =
        M51EventCopy.identify slice tau r.1 (hTau r.1 r.2.2) (S.identify r z) :=
    M51EventCopy.diffeomorph_apply slice (hTau p S.ordered.le).symm
      (hTau r.1 r.2.2).symm (S.identify r) z
  have hsource : y = M51EventCopy.identify slice tau s.1 (hTau s.1 s.2.2) x :=
    eq_of_heq (hy.trans (M51EventCopy.identify_apply_heq slice tau s.1
      (hTau s.1 s.2.2) x).symm)
  have hinverse : (S'.identify s).symm y = c ((S.identify s).symm x) := by
    apply (S'.identify s).injective
    change (S'.identify s) ((S'.identify s).symm y) =
      (S'.identify s) (c ((S.identify s).symm x))
    rw [Diffeomorph.apply_symm_apply, hmap, Diffeomorph.apply_symm_apply]
    exact hsource
  change HEq (S'.identify t ((S'.identify s).symm y)) _
  rw [hinverse, hmap]
  exact M51EventCopy.identify_apply_heq slice tau t.1 (hTau t.1 t.2.2) _

end PoincareConjecture.SurgeryRegularSlab
