import PoincareConjecture.Proofs.M44.Mathlib.SpatialJetsWithin
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Piecewise

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

theorem continuousOn_timeJoin {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    {a T b : ℝ} {U : Set V}
    {f g : ℝ × V → W}
    (hf : ContinuousOn f (Ioc a T ×ˢ U))
    (hg : ContinuousOn g (Icc T b ×ˢ U))
    (hjoin : ∀ x ∈ U, f (T, x) = g (T, x)) :
    ContinuousOn (fun p : ℝ × V => if p.1 < T then f p else g p) (Ioc a b ×ˢ U) := by
  have hclosed_left : closure {p : ℝ × V | p.1 < T} ⊆ {p | p.1 ≤ T} :=
    closure_minimal (fun p h => (show p.1 < T from h).le)
      (isClosed_le continuous_fst continuous_const)
  have hclosed_right : closure {p : ℝ × V | ¬p.1 < T} ⊆ {p | T ≤ p.1} :=
    closure_minimal (fun _ h => le_of_not_gt h) (isClosed_le continuous_const continuous_fst)
  apply ContinuousOn.if
  · intro p hp
    have hfront := continuous_fst.frontier_preimage_subset (Iio T) hp.2
    have heq : p.1 = T := by simpa only [frontier_Iio, mem_preimage, mem_singleton_iff] using hfront
    simpa only [← heq] using hjoin p.2 hp.1.2
  · exact hf.mono fun p hp => ⟨⟨hp.1.1.1, hclosed_left hp.2⟩, hp.1.2⟩
  · exact hg.mono fun p hp => ⟨⟨hclosed_right hp.2, hp.1.1.2⟩, hp.1.2⟩

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem timeJoin_spatialJets {a T b : ℝ} (hTb : T < b) {U : Set V}
    (hU : IsOpen U) {f g : ℝ × V → W}
    (hf : ContDiffOn ℝ ∞ f (Ioc a T ×ˢ U))
    (hg : ContDiffOn ℝ ∞ g (Icc T b ×ˢ U))
    (hjoin : ∀ x ∈ U, f (T, x) = g (T, x)) (m : ℕ) :
    ContinuousOn (fun p : ℝ × V => iteratedFDeriv ℝ m
      (fun x => if p.1 < T then f (p.1, x) else g (p.1, x)) p.2)
      (Ioc a b ×ˢ U) := by
  have hfjet := (M44.contDiffOn_spatialJet_within hf (uniqueDiffOn_Ioc a T) hU m).continuousOn
  have hgjet := (M44.contDiffOn_spatialJet_within hg (uniqueDiffOn_Icc hTb) hU m).continuousOn
  have heq (x : V) (hx : x ∈ U) :
      iteratedFDeriv ℝ m (fun y => f (T, y)) x =
        iteratedFDeriv ℝ m (fun y => g (T, y)) x := by
    have h : (fun y => f (T, y)) =ᶠ[𝓝 x] (fun y => g (T, y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hjoin y hy
    exact (h.iteratedFDeriv ℝ m).eq_of_nhds
  have h := continuousOn_timeJoin hfjet hgjet heq
  apply h.congr
  intro p _
  by_cases ht : p.1 < T <;> simp [ht]

theorem timeJoin_smooth_finalEndpoint {a T b : ℝ} (hTb : T < b)
    {U : Set V} (hU : IsOpen U) {f g : ℝ × V → W}
    (hinterior : ContDiffOn ℝ ∞ (fun p => if p.1 < T then f p else g p) (Ioo a b ×ˢ U))
    (hg : ContDiffOn ℝ ∞ g (Icc T b ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p => if p.1 < T then f p else g p) (Ioc a b ×ˢ U) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  by_cases htb : t < b
  · exact (hinterior.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds
      ⟨⟨ht.1, htb⟩, hx⟩)).contDiffWithinAt
  · have heq : t = b := le_antisymm ht.2 (le_of_not_gt htb)
    subst t
    have hT : {p : ℝ × V | T < p.1} ∈ 𝓝[Ioc a b ×ˢ U] (b, x) :=
      mem_nhdsWithin_of_mem_nhds
        ((continuous_fst.isOpen_preimage _ isOpen_Ioi).mem_nhds hTb)
    have hdomain : Icc T b ×ˢ U ∈ 𝓝[Ioc a b ×ˢ U] (b, x) := by
      filter_upwards [self_mem_nhdsWithin, hT] with p hp hpT
      exact ⟨⟨hpT.le, hp.1.2⟩, hp.2⟩
    have h := (hg (b, x) ⟨⟨hTb.le, le_rfl⟩, hx⟩).mono_of_mem_nhdsWithin hdomain
    apply h.congr_of_eventuallyEq
    · filter_upwards [hT] with p hp
      exact if_neg (not_lt_of_gt hp)
    · exact if_neg (not_lt_of_gt hTb)

end PoincareConjecture.M45
