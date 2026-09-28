import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith










set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D



theorem exists_periodic_injection_tolerance {Z E : Type*}
    [TopologicalSpace Z] [MetricSpace E] {K : Set Z} (hK : IsCompact K)
    {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (_hrT : r < T / 2)
    (f : Z → ℝ → E)
    (hf : ContinuousOn (fun p : Z × ℝ => f p.1 p.2) (K ×ˢ Icc 0 T))
    (hper : ∀ z ∈ K, Periodic (f z) T)
    (hinj : ∀ z ∈ K, InjOn (f z) (Ico 0 T)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Z → ℝ → E,
      (∀ z ∈ K, Periodic (g z) T) →
      (∀ z ∈ K, ∀ t ∈ Icc 0 T, dist (g z t) (f z t) < ε) →
      (∀ z ∈ K, ∀ s t : ℝ, |s - t| < r → g z s = g z t → s = t) →
      ∀ z ∈ K, InjOn (g z) (Ico 0 T) := by
  let C : Set (Z × (ℝ × ℝ)) :=
    (K ×ˢ (Icc 0 T ×ˢ Icc 0 T)) ∩
      {p | r ≤ |p.2.1 - p.2.2| ∧ |p.2.1 - p.2.2| ≤ T - r}
  have hC : IsCompact C :=
    (hK.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      ((isClosed_le continuous_const (continuous_snd.fst.sub continuous_snd.snd).abs).inter
        (isClosed_le (continuous_snd.fst.sub continuous_snd.snd).abs continuous_const))
  have hf₁ : ContinuousOn (fun p : Z × (ℝ × ℝ) => f p.1 p.2.1) C :=
    hf.comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
      (fun _ hp => ⟨hp.1.1, hp.1.2.1⟩)
  have hf₂ : ContinuousOn (fun p : Z × (ℝ × ℝ) => f p.1 p.2.2) C :=
    hf.comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
      (fun _ hp => ⟨hp.1.1, hp.1.2.2⟩)
  have hd : ContinuousOn (fun p : Z × (ℝ × ℝ) => dist (f p.1 p.2.1) (f p.1 p.2.2)) C :=
    continuous_dist.continuousOn.comp (hf₁.prodMk hf₂) (mapsTo_univ _ _)
  have hpos : ∀ p ∈ C, 0 < dist (f p.1 p.2.1) (f p.1 p.2.2) := by
    rintro ⟨z, s, t⟩ ⟨⟨hz, hs, ht⟩, hgap⟩
    change r ≤ |s - t| ∧ |s - t| ≤ T - r at hgap
    apply dist_pos.mpr
    intro heq
    have hTzero : f z T = f z 0 := by simpa only [zero_add] using hper z hz 0
    by_cases hsT : s = T
    · subst s
      rw [hTzero] at heq
      by_cases htT : t = T
      · subst t
        simp only [sub_self, abs_zero] at hgap
        linarith [hgap.1]
      · have ht0 : t = 0 := (hinj z hz ⟨le_rfl, hT⟩
          ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩ heq).symm
        subst t
        simp only [sub_zero, abs_of_pos hT] at hgap
        linarith [hgap.2]
    · have hs' : s ∈ Ico 0 T := ⟨hs.1, lt_of_le_of_ne hs.2 hsT⟩
      by_cases htT : t = T
      · subst t
        rw [hTzero] at heq
        have hs0 : s = 0 := hinj z hz hs' ⟨le_rfl, hT⟩ heq
        subst s
        simp only [zero_sub, abs_neg, abs_of_pos hT] at hgap
        linarith [hgap.2]
      · have hst : s = t := hinj z hz hs' ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩ heq
        subst t
        simp only [sub_self, abs_zero] at hgap
        linarith [hgap.1]
  obtain ⟨η, hη, hηle⟩ := hC.exists_forall_le' hd hpos
  refine ⟨η / 3, by linarith, ?_⟩
  intro g hgper hclose hlocal z hz s hs t ht heq
  by_cases hnear : |s - t| < r
  · exact hlocal z hz s t hnear heq
  · have hfar : r ≤ |s - t| := le_of_not_gt hnear
    by_cases hupper : |s - t| ≤ T - r
    · have hgap := hηle (z, s, t)
        ⟨⟨hz, ⟨hs.1, hs.2.le⟩, ⟨ht.1, ht.2.le⟩⟩, hfar, hupper⟩
      have hleft : dist (f z s) (g z s) < η / 3 := by
        rw [dist_comm]
        exact hclose z hz s ⟨hs.1, hs.2.le⟩
      have hright : dist (g z s) (f z t) < η / 3 := by
        rw [heq]
        exact hclose z hz t ⟨ht.1, ht.2.le⟩
      linarith [dist_triangle (f z s) (g z s) (f z t)]
    · by_cases hst : s ≤ t
      · have hwrapped : |(s + T) - t| < r := by
          rw [abs_of_nonneg (by linarith [hs.1, ht.2])]
          rw [abs_of_nonpos (sub_nonpos.mpr hst)] at hupper
          linarith
        have heq' := hlocal z hz (s + T) t hwrapped ((hgper z hz s).trans heq)
        linarith [hs.1, ht.2]
      · have hwrapped : |(t + T) - s| < r := by
          rw [abs_of_nonneg (by linarith [ht.1, hs.2])]
          rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hst))] at hupper
          linarith
        have heq' := hlocal z hz (t + T) s hwrapped ((hgper z hz t).trans heq.symm)
        linarith [ht.1, hs.2]

end PoincareConjecture.M25.Topology3D
