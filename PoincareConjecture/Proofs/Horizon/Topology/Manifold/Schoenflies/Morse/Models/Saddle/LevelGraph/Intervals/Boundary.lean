import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Completion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exterior_completion_boundary
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source)
    (H : S2 → Real)
    (hgerm : ∀ q ∈ connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r,
      H =ᶠ[𝓝 q] h) :
    let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
    let B := range (fun i : Fin 2 × Fin 2 => e (contact r i))
    B ⊆ K ∧
      (∀ q ∈ K \ B, ∃ W : Set S2, IsOpen W ∧ q ∈ W ∧ W ∩ H ⁻¹' {h p} ⊆ K) ∧
      ∀ q ∈ B, ∃ (δ : Real) (α : Real → S2), 0 < δ ∧
        ContinuousOn α (Ioo (-δ) δ) ∧ α 0 = q ∧ InjOn α (Ioo (-δ) δ) ∧
        α '' Ioo (-δ) δ ⊆ H ⁻¹' {h p} ∧
        ∀ t ∈ Ioo (-δ) δ, α t ∈ K ↔ 0 ≤ t := by
  let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
  let B := range (fun i : Fin 2 × Fin 2 => e (contact r i))
  obtain ⟨_, hboundary, _, _, _, _⟩ :=
    compact_regular_exterior hh hunique e he0 hep hform hr hrs
  have hBK : B ⊆ K := by
    change range (fun i => e (contact r i)) ⊆ K
    rw [← hboundary]
    exact inter_subset_left
  obtain ⟨O, hO, hCO, hlevel⟩ :=
    exists_open_isolating_neighborhood hh hunique e he0 hep hform
  have hclosed : IsClosed (e '' closedSquare r) :=
    ((isCompact_closedSquare hr.le).image_of_continuousOn (e.continuousOn.mono hrs)).isClosed
  refine ⟨hBK, ?_, ?_⟩
  · intro q hq
    obtain ⟨V, hVeq, hV, hqV⟩ := _root_.mem_nhds_iff.mp (hgerm q hq.1)
    have hqout : q ∉ e '' closedSquare r := by
      intro hqp
      exact hq.2 (hboundary ▸ (show q ∈ K ∩ e '' closedSquare r from ⟨hq.1, hqp⟩))
    refine ⟨(O \ e '' closedSquare r) ∩ V,
      (hO.inter hclosed.isOpen_compl).inter hV, ⟨⟨hCO hq.1.1, hqout⟩, hqV⟩, ?_⟩
    rintro y ⟨⟨⟨hyO, hyout⟩, hyV⟩, hyH⟩
    have hyh : h y = h p := (hVeq hyV).symm.trans hyH
    refine ⟨hlevel ▸ (show y ∈ O ∩ h ⁻¹' {h p} from ⟨hyO, hyh⟩), ?_⟩
    exact fun hy => hyout (image_mono (openSquare_subset_closedSquare r) hy)
  · rintro q ⟨i, rfl⟩
    obtain ⟨δ, hδ, _, W, _, _, hα, hinj, hαlevel, _, _, hhalf⟩ :=
      exists_contact_halfInterval e he hei hr hrs hform i
    let α : Real → S2 := fun t => e ((1 + t) • contact r i)
    have hα0 : α 0 = e (contact r i) := by simp [α]
    have hzero : (0 : Real) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
    have hcont : ContinuousAt α 0 :=
      hα.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hzero)
    have hevent : ∀ᶠ t in 𝓝 (0 : Real), H (α t) = h (α t) :=
      hcont.eventually (by simpa [α, Filter.EventuallyEq] using hgerm _ (hBK ⟨i, rfl⟩))
    obtain ⟨s, hs, hseq⟩ := Metric.eventually_nhds_iff.mp hevent
    let d := min δ s / 2
    have hd : 0 < d := half_pos (lt_min hδ hs)
    have hdδ : d < δ := lt_of_lt_of_le (half_lt_self (lt_min hδ hs)) (min_le_left _ _)
    have hds : d < s := lt_of_lt_of_le (half_lt_self (lt_min hδ hs)) (min_le_right _ _)
    have hsub : Ioo (-d) d ⊆ Ioo (-δ) δ := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨d, α, hd, hα.continuousOn.mono hsub, hα0, hinj.mono hsub, ?_, ?_⟩
    · rintro y ⟨t, ht, rfl⟩
      change H (α t) = h p
      rw [hseq (show dist t 0 < s by
        rw [Real.dist_eq, sub_zero, abs_lt]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
      exact (hαlevel.symm ▸ mem_image_of_mem α (hsub ht)).2
    · intro t ht
      simpa only [hep] using hhalf t (hsub ht)

end Poincare.Manifold.Schoenflies.SaddleLevel
