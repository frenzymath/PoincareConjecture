import PoincareConjecture.Statements.Ch04.Continuation
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M51Ordinary

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def initialLifetimes (g0 : RiemannianMetric n M) : Set ℝ :=
  {T | 0 < T ∧ ∃ F : RicciFlow n M (Ico 0 T), F.metric 0 = g0}

def initialDomain (g0 : RiemannianMetric n M) : Set ℝ :=
  {t | 0 ≤ t ∧ ∃ T ∈ initialLifetimes g0, t < T}

theorem initialLifetimes_nonempty (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) : (initialLifetimes g0).Nonempty := by
  obtain ⟨T, hT, F, hF⟩ := h03.1 g0
  exact ⟨T, hT, F, hF⟩

theorem initialDomain_of_mem_lifetime (g0 : RiemannianMetric n M) {T : ℝ}
    (hT : T ∈ initialLifetimes g0) : Ico 0 T ⊆ initialDomain g0 :=
  fun _ ht => ⟨ht.1, T, hT, ht.2⟩

theorem initialDomain_isLeast (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) : IsLeast (initialDomain g0) 0 := by
  obtain ⟨T, hT⟩ := initialLifetimes_nonempty h03 g0
  exact ⟨⟨le_rfl, T, hT, hT.1⟩, fun _ ht => ht.1⟩

theorem initialDomain_ordConnected (g0 : RiemannianMetric n M) :
    (initialDomain g0).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  obtain ⟨T, hT, hyT⟩ := hy.2
  exact ⟨hx.1.trans hz.1, T, hT, hz.2.trans_lt hyT⟩

theorem initialDomain_nontrivial (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) : (initialDomain g0).Nontrivial := by
  obtain ⟨T, hT⟩ := initialLifetimes_nonempty h03 g0
  refine ⟨0, (initialDomain_isLeast h03 g0).1, T / 2,
    initialDomain_of_mem_lifetime g0 hT ⟨?_, ?_⟩, ?_⟩ <;> linarith [hT.1]

theorem initialDomain_later (g0 : RiemannianMetric n M) {t : ℝ}
    (ht : t ∈ initialDomain g0) : ∃ s ∈ initialDomain g0, t < s := by
  obtain ⟨T, hT, htT⟩ := ht.2
  refine ⟨(t + T) / 2, initialDomain_of_mem_lifetime g0 hT ⟨?_, ?_⟩, ?_⟩ <;>
    linarith [ht.1]

structure InitialCandidate (g0 : RiemannianMetric n M) where
  lifetime : ℝ
  lifetime_pos : 0 < lifetime
  flow : RicciFlow n M (Ico 0 lifetime)
  initial_metric : flow.metric 0 = g0

theorem InitialCandidate.mem_lifetimes {g0 : RiemannianMetric n M}
    (C : InitialCandidate g0) : C.lifetime ∈ initialLifetimes g0 :=
  ⟨C.lifetime_pos, C.flow, C.initial_metric⟩

theorem initialCandidate_exists_at (g0 : RiemannianMetric n M) {t : ℝ}
    (ht : t ∈ initialDomain g0) : ∃ C : InitialCandidate g0, t < C.lifetime := by
  obtain ⟨T, hT, htT⟩ := ht.2
  obtain ⟨F, hF⟩ := hT.2
  exact ⟨⟨T, hT.1, F, hF⟩, htT⟩

noncomputable def initialCandidate (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) : InitialCandidate g0 :=
  Classical.choice (by
    obtain ⟨T, hT, F, hF⟩ := h03.1 g0
    exact ⟨⟨T, hT, F, hF⟩⟩)

noncomputable def initialCandidateAt (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (t : ℝ) : InitialCandidate g0 := by
  classical
  exact if ht : t ∈ initialDomain g0 then
    Classical.choose (initialCandidate_exists_at g0 ht)
  else initialCandidate h03 g0

theorem initialCandidateAt_contains (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) {t : ℝ} (ht : t ∈ initialDomain g0) :
    t ∈ Ico 0 (initialCandidateAt h03 g0 t).lifetime := by
  refine ⟨ht.1, ?_⟩
  simpa only [initialCandidateAt, dif_pos ht] using
    Classical.choose_spec (initialCandidate_exists_at g0 ht)

theorem initialCandidate_metric_agreement (h03 : RicciFlowLocalTheory n M)
    {g0 : RiemannianMetric n M} (C C' : InitialCandidate g0) {t : ℝ}
    (ht : t ∈ Ico 0 C.lifetime) (ht' : t ∈ Ico 0 C'.lifetime) :
    C.flow.metric t = C'.flow.metric t :=
  h03.2.1 (Ico 0 C.lifetime) (Ico 0 C'.lifetime) C.flow C'.flow
    ⟨⟨le_rfl, C.lifetime_pos⟩, fun _ hs => hs.1⟩
    ⟨⟨le_rfl, C'.lifetime_pos⟩, fun _ hs => hs.1⟩
    (C.initial_metric.trans C'.initial_metric.symm) ⟨ht, ht'⟩

noncomputable def initialUnionData (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (t : ℝ) :
    Σ g : RiemannianMetric n M, LeviCivitaData g :=
  ⟨(initialCandidateAt h03 g0 t).flow.metric t,
    (initialCandidateAt h03 g0 t).flow.connection t⟩

noncomputable def initialUnionMetric (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (t : ℝ) : RiemannianMetric n M :=
  (initialUnionData h03 g0 t).1

noncomputable def initialUnionConnection (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (t : ℝ) :
    LeviCivitaData (initialUnionMetric h03 g0 t) :=
  (initialUnionData h03 g0 t).2

theorem initialUnionMetric_eq_candidate (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (C : InitialCandidate g0) :
    EqOn (initialUnionMetric h03 g0) C.flow.metric (Ico 0 C.lifetime) := by
  intro t ht
  have hD := initialDomain_of_mem_lifetime g0 C.mem_lifetimes ht
  exact initialCandidate_metric_agreement h03 (initialCandidateAt h03 g0 t) C
    (initialCandidateAt_contains h03 g0 hD) ht

theorem initialUnionMetric_smooth (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) :
    RiemannianMetric.IsSmoothFamilyOn (initialUnionMetric h03 g0) (initialDomain g0) := by
  unfold RiemannianMetric.IsSmoothFamilyOn
  apply contMDiffOn_of_locally_contMDiffOn
  intro p hp
  let C := initialCandidateAt h03 g0 p.1
  let U : Set (ℝ × M) := {q | q.1 < C.lifetime}
  have hpC : p.1 ∈ Ico 0 C.lifetime := initialCandidateAt_contains h03 g0 hp.1
  refine ⟨U, isOpen_Iio.preimage continuous_fst, hpC.2, ?_⟩
  have hf := C.flow.smooth
  unfold RiemannianMetric.IsSmoothFamilyOn at hf
  refine (hf.mono (t := (initialDomain g0 ×ˢ univ) ∩ U) ?_).congr ?_
  · intro q hq
    exact ⟨⟨hq.1.1.1, hq.2⟩, mem_univ _⟩
  · intro q hq
    rw [initialUnionMetric_eq_candidate h03 g0 C ⟨hq.1.1.1, hq.2⟩]

theorem initialUnion_equation (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (t : ℝ) (ht : t ∈ initialDomain g0)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (initialUnionMetric h03 g0 s).inner x v w)
      (-2 * (initialUnionConnection h03 g0 t).ricci x v w) (initialDomain g0) t := by
  let C := initialCandidateAt h03 g0 t
  have htC : t ∈ Ico 0 C.lifetime := initialCandidateAt_contains h03 g0 ht
  have hlocal : Ico 0 C.lifetime ∈ 𝓝[initialDomain g0] t :=
    mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds htC.2))
      (fun _ hs => ⟨hs.1.1, hs.2⟩)
  have he := C.flow.equation t htC x v w
  apply (he.mono_of_mem_nhdsWithin hlocal).congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [hlocal] with s hs
  rw [initialUnionMetric_eq_candidate h03 g0 C hs]

noncomputable def initialUnion (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) : RicciFlow n M (initialDomain g0) where
  metric := initialUnionMetric h03 g0
  connection := initialUnionConnection h03 g0
  interval := initialDomain_ordConnected g0
  nontrivial := initialDomain_nontrivial h03 g0
  smooth := initialUnionMetric_smooth h03 g0
  equation := initialUnion_equation h03 g0

theorem initialUnion_metric_eq (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow n M (Ico 0 T)) (hF : F.metric 0 = g0) :
    EqOn (initialUnion h03 g0).metric F.metric (Ico 0 T) :=
  initialUnionMetric_eq_candidate h03 g0 ⟨T, hT, F, hF⟩

@[simp] theorem initialUnion_initial_metric (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) : (initialUnion h03 g0).metric 0 = g0 := by
  let C := initialCandidate h03 g0
  exact (initialUnionMetric_eq_candidate h03 g0 C ⟨le_rfl, C.lifetime_pos⟩).trans
    C.initial_metric

end PoincareConjecture.M51Ordinary
