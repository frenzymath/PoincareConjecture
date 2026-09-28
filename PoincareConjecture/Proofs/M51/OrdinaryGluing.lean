import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M51Ordinary

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a T B : ℝ}

noncomputable def overlapData (F : RicciFlow n M (Ico 0 T))
    (G : RicciFlow n M (Ico a B)) (c t : ℝ) :
    Σ g : RiemannianMetric n M, LeviCivitaData g :=
  if t < c then ⟨F.metric t, F.connection t⟩ else ⟨G.metric t, G.connection t⟩

noncomputable def overlapMetric (F : RicciFlow n M (Ico 0 T))
    (G : RicciFlow n M (Ico a B)) (c t : ℝ) : RiemannianMetric n M :=
  (overlapData F G c t).1

noncomputable def overlapConnection (F : RicciFlow n M (Ico 0 T))
    (G : RicciFlow n M (Ico a B)) (c t : ℝ) :
    LeviCivitaData (overlapMetric F G c t) :=
  (overlapData F G c t).2

variable (F : RicciFlow n M (Ico 0 T)) (G : RicciFlow n M (Ico a B))
  (c : ℝ)

theorem overlapMetric_eq_left (hac : a < c)
    (hmetric : EqOn F.metric G.metric (Ico a T)) :
    EqOn (overlapMetric F G c) F.metric (Ico 0 T) := by
  intro t ht
  by_cases htc : t < c
  · simp only [overlapMetric, overlapData, if_pos htc]
  · simpa only [overlapMetric, overlapData, if_neg htc] using
      (hmetric ⟨hac.le.trans (le_of_not_gt htc), ht.2⟩).symm

theorem overlapMetric_eq_right (hcT : c < T)
    (hmetric : EqOn F.metric G.metric (Ico a T)) :
    EqOn (overlapMetric F G c) G.metric (Ico a B) := by
  intro t ht
  by_cases htc : t < c
  · simpa only [overlapMetric, overlapData, if_pos htc] using
      hmetric ⟨ht.1, htc.trans hcT⟩
  · simp only [overlapMetric, overlapData, if_neg htc]

theorem overlapConnection_ricci_left {t : ℝ} (htc : t < c)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (overlapConnection F G c t).ricci x v w = (F.connection t).ricci x v w := by
  have hd : overlapData F G c t = ⟨F.metric t, F.connection t⟩ := if_pos htc
  exact congrArg (fun p : Σ g : RiemannianMetric n M, LeviCivitaData g =>
    p.2.ricci x v w) hd

theorem overlapConnection_ricci_right {t : ℝ} (hct : c ≤ t)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (overlapConnection F G c t).ricci x v w = (G.connection t).ricci x v w := by
  have hd : overlapData F G c t = ⟨G.metric t, G.connection t⟩ :=
    if_neg (not_lt.mpr hct)
  exact congrArg (fun p : Σ g : RiemannianMetric n M, LeviCivitaData g =>
    p.2.ricci x v w) hd

theorem overlapMetric_smooth (hc : c ∈ Ioo a T)
    (hmetric : EqOn F.metric G.metric (Ico a T)) :
    RiemannianMetric.IsSmoothFamilyOn (overlapMetric F G c) (Ico 0 B) := by
  unfold RiemannianMetric.IsSmoothFamilyOn
  apply contMDiffOn_of_locally_contMDiffOn
  intro p hp
  by_cases hpc : p.1 < c
  · let U : Set (ℝ × M) := {q | q.1 < T}
    refine ⟨U, isOpen_Iio.preimage continuous_fst, hpc.trans hc.2, ?_⟩
    have hf := F.smooth
    unfold RiemannianMetric.IsSmoothFamilyOn at hf
    refine (hf.mono (t := (Ico 0 B ×ˢ univ) ∩ U) ?_).congr ?_
    · intro q hq
      exact ⟨⟨hq.1.1.1, hq.2⟩, mem_univ _⟩
    · intro q hq
      rw [overlapMetric_eq_left F G c hc.1 hmetric ⟨hq.1.1.1, hq.2⟩]
  · let U : Set (ℝ × M) := {q | a < q.1}
    refine ⟨U, isOpen_Ioi.preimage continuous_fst,
      hc.1.trans_le (le_of_not_gt hpc), ?_⟩
    have hg := G.smooth
    unfold RiemannianMetric.IsSmoothFamilyOn at hg
    refine (hg.mono (t := (Ico 0 B ×ˢ univ) ∩ U) ?_).congr ?_
    · intro q hq
      exact ⟨⟨hq.2.le, hq.1.1.2⟩, mem_univ _⟩
    · intro q hq
      rw [overlapMetric_eq_right F G c hc.2 hmetric ⟨hq.2.le, hq.1.1.2⟩]

theorem overlap_equation (hc : c ∈ Ioo a T)
    (hmetric : EqOn F.metric G.metric (Ico a T))
    (t : ℝ) (ht : t ∈ Ico 0 B) (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (overlapMetric F G c s).inner x v w)
      (-2 * (overlapConnection F G c t).ricci x v w) (Ico 0 B) t := by
  by_cases htc : t < c
  · have hlocal : Ico 0 T ∈ 𝓝[Ico 0 B] t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds (htc.trans hc.2)))
        (fun _ hs => ⟨hs.1.1, hs.2⟩)
    rw [overlapConnection_ricci_left F G c htc]
    have he := F.equation t ⟨ht.1, htc.trans hc.2⟩ x v w
    apply (he.mono_of_mem_nhdsWithin hlocal).congr_of_eventuallyEq_of_mem ?_ ht
    filter_upwards [hlocal] with s hs
    rw [overlapMetric_eq_left F G c hc.1 hmetric hs]
  · have hct : c ≤ t := le_of_not_gt htc
    have hlocal : Ico a B ∈ 𝓝[Ico 0 B] t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds (hc.1.trans_le hct)))
        (fun _ hs => ⟨hs.2.le, hs.1.2⟩)
    rw [overlapConnection_ricci_right F G c hct]
    have he := G.equation t ⟨hc.1.le.trans hct, ht.2⟩ x v w
    apply (he.mono_of_mem_nhdsWithin hlocal).congr_of_eventuallyEq_of_mem ?_ ht
    filter_upwards [hlocal] with s hs
    rw [overlapMetric_eq_right F G c hc.2 hmetric hs]

noncomputable def glueOverlap (ha : 0 < a) (hc : c ∈ Ioo a T) (hTB : T < B)
    (hmetric : EqOn F.metric G.metric (Ico a T)) : RicciFlow n M (Ico 0 B) where
  metric := overlapMetric F G c
  connection := overlapConnection F G c
  interval := ordConnected_Ico
  nontrivial := ⟨0, ⟨le_rfl, ha.trans (hc.1.trans (hc.2.trans hTB))⟩,
    a, ⟨ha.le, hc.1.trans (hc.2.trans hTB)⟩, ha.ne⟩
  smooth := overlapMetric_smooth F G c hc hmetric
  equation := overlap_equation F G c hc hmetric

theorem glueOverlap_metric_left (ha : 0 < a) (hc : c ∈ Ioo a T) (hTB : T < B)
    (hmetric : EqOn F.metric G.metric (Ico a T)) :
    EqOn (glueOverlap F G c ha hc hTB hmetric).metric F.metric (Ico 0 T) :=
  overlapMetric_eq_left F G c hc.1 hmetric

theorem glueOverlap_metric_right (ha : 0 < a) (hc : c ∈ Ioo a T) (hTB : T < B)
    (hmetric : EqOn F.metric G.metric (Ico a T)) :
    EqOn (glueOverlap F G c ha hc hTB hmetric).metric G.metric (Ico a B) :=
  overlapMetric_eq_right F G c hc.2 hmetric

@[simp] theorem glueOverlap_initial_metric (ha : 0 < a) (hc : c ∈ Ioo a T)
    (hTB : T < B) (hmetric : EqOn F.metric G.metric (Ico a T)) :
    (glueOverlap F G c ha hc hTB hmetric).metric 0 = F.metric 0 :=
  glueOverlap_metric_left F G c ha hc hTB hmetric ⟨le_rfl, ha.trans (hc.1.trans hc.2)⟩

theorem glueOverlap_isLeast (ha : 0 < a) (hc : c ∈ Ioo a T) (hTB : T < B) :
    IsLeast (Ico 0 B) 0 :=
  ⟨⟨le_rfl, ha.trans (hc.1.trans (hc.2.trans hTB))⟩, fun _ ht => ht.1⟩

end PoincareConjecture.M51Ordinary
