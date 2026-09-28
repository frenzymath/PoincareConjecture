import PoincareConjecture.Statements.Ch04.Continuation
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_flow_of_initial_cover
    (hunique : RicciFlowUniqueness n M) (g₀ : RiemannianMetric n M)
    {S : ℝ} (hS : 0 < S)
    (hcover : ∀ t ∈ Ico 0 S, ∃ T : ℝ, t < T ∧ 0 < T ∧
      ∃ F : RicciFlow n M (Ico 0 T), F.metric 0 = g₀) :
    ∃ F : RicciFlow n M (Ico 0 S), F.metric 0 = g₀ := by
  classical
  choose tau htime hpos flow hinit using hcover
  have hzero : (0 : ℝ) ∈ Ico 0 S := ⟨le_rfl, hS⟩
  let d (t : ℝ) : (T : ℝ) × RicciFlow n M (Ico 0 T) :=
    if ht : t ∈ Ico 0 S then ⟨tau t ht, flow t ht⟩
    else ⟨tau 0 hzero, flow 0 hzero⟩
  have hd (t : ℝ) (ht : t ∈ Ico 0 S) :
      0 < (d t).1 ∧ t < (d t).1 ∧ (d t).2.metric 0 = g₀ := by
    have hdt : d t = ⟨tau t ht, flow t ht⟩ := dif_pos ht
    rw [hdt]
    exact ⟨hpos t ht, htime t ht, hinit t ht⟩
  let g (t : ℝ) := (d t).2.metric t
  have heq (s t : ℝ) (hs : s ∈ Ico 0 S) (ht : t ∈ Ico 0 S)
      (hst : s < (d t).1) : g s = (d t).2.metric s := by
    apply hunique (Ico 0 (d s).1) (Ico 0 (d t).1) (d s).2 (d t).2
      ⟨⟨le_rfl, (hd s hs).1⟩, fun _ hx => hx.1⟩
      ⟨⟨le_rfl, (hd t ht).1⟩, fun _ hx => hx.1⟩
      ((hd s hs).2.2.trans (hd t ht).2.2.symm)
    exact ⟨⟨hs.1, (hd s hs).2.1⟩, ⟨hs.1, hst⟩⟩
  let F : RicciFlow n M (Ico 0 S) :=
    { metric := g
      connection := fun t => (d t).2.connection t
      interval := ordConnected_Ico
      nontrivial := ⟨0, hzero, S / 2, ⟨by linarith, by linarith⟩, by linarith⟩
      smooth := by
        intro p hp
        have hnear : Ico 0 (d p.1).1 ×ˢ (univ : Set M) ∈
            𝓝[Ico 0 S ×ˢ univ] p := by
          have hlt := (continuous_fst.tendsto p).eventually
            (gt_mem_nhds (hd p.1 hp.1).2.1)
          filter_upwards [self_mem_nhdsWithin,
            hlt.filter_mono nhdsWithin_le_nhds] with q hq hqt
          exact ⟨⟨hq.1.1, hqt⟩, mem_univ _⟩
        have hsm := (d p.1).2.smooth p
          ⟨⟨hp.1.1, (hd p.1 hp.1).2.1⟩, mem_univ _⟩
        apply (hsm.mono_of_mem_nhdsWithin hnear).congr_of_eventuallyEq_of_mem _ hp
        filter_upwards [self_mem_nhdsWithin, hnear] with q hq hqt
        rw [heq q.1 p.1 hq.1 hp.1 hqt.1.2]
      equation := by
        intro t ht x v w
        have hnear : Ico 0 (d t).1 ∈ 𝓝[Ico 0 S] t := by
          filter_upwards [self_mem_nhdsWithin,
            (gt_mem_nhds (hd t ht).2.1).filter_mono nhdsWithin_le_nhds] with s hs hst
          exact ⟨hs.1, hst⟩
        have hderiv := (d t).2.equation t ⟨ht.1, (hd t ht).2.1⟩ x v w
        apply (hderiv.mono_of_mem_nhdsWithin hnear).congr_of_eventuallyEq _ rfl
        filter_upwards [self_mem_nhdsWithin, hnear] with s hs hst
        rw [heq s t hs ht hst.2] }
  exact ⟨F, (hd 0 hzero).2.2⟩

theorem exists_long_flow_of_uniform_curvature
    (hlocal : RicciFlowLocalTheory n M) (g₀ : RiemannianMetric n M)
    {B C : ℝ}
    (hbound : ∀ T : ℝ, 0 < T → T ≤ B →
      ∀ F : RicciFlow n M (Ico 0 T), F.metric 0 = g₀ →
        ∀ t ∈ Ico 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ C) :
    ∃ T : ℝ, B < T ∧ 0 < T ∧
      ∃ F : RicciFlow n M (Ico 0 T), F.metric 0 = g₀ := by
  classical
  by_contra hno
  let E : Set ℝ := {T | 0 < T ∧
    ∃ F : RicciFlow n M (Ico 0 T), F.metric 0 = g₀}
  obtain ⟨T₀, hT₀, F₀, hF₀⟩ := hlocal.1 g₀
  have hE : T₀ ∈ E := ⟨hT₀, F₀, hF₀⟩
  have hupper : ∀ T ∈ E, T ≤ B := by
    intro T hT
    by_contra hle
    exact hno ⟨T, lt_of_not_ge hle, hT⟩
  have hbdd : BddAbove E := ⟨B, hupper⟩
  have hS : 0 < sSup E := hT₀.trans_le (le_csSup hbdd hE)
  have hSB : sSup E ≤ B := csSup_le ⟨T₀, hE⟩ hupper
  obtain ⟨F, hF⟩ := exists_flow_of_initial_cover hlocal.2.1 g₀ hS (by
    intro t ht
    obtain ⟨T, hT, htT⟩ := exists_lt_of_lt_csSup ⟨T₀, hE⟩ ht.2
    exact ⟨T, htT, hT⟩)
  obtain ⟨T', hT', F', hFF'⟩ := hlocal.2.2 (sSup E) hS F
    ⟨C, hbound (sSup E) hS hSB F hF⟩
  have hF' : F'.metric 0 = g₀ := (hFF' ⟨le_rfl, hS⟩).symm.trans hF
  exact (not_lt_of_ge (le_csSup hbdd ⟨hS.trans hT', F', hF'⟩)) hT'

end PoincareConjecture.M45
