import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.Topology

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

theorem Saddle.Caps.exists_terminal_collar_in
    (T : OpenPartialHomeomorph (S1 × Real) S2) {g : S2 → E3} (hg : Continuous g)
    {c : Real} (hs : ∀ q : S1, (q, c) ∈ T.source)
    {U : Set E3} (hU : IsOpen U) (hcU : ∀ q : S1, g (T (q, c)) ∈ U) :
    ∃ ε : Real, 0 < ε ∧ g '' (T '' (univ ×ˢ Icc (c - ε) (c + ε))) ⊆ U := by
  have hnear : ∀ᶠ t in 𝓝 c, ∀ q : S1, g (T (q, t)) ∈ U := by
    have hh := (isCompact_univ : IsCompact (univ : Set S1)).eventually_forall_of_forall_eventually
      (x₀ := c) (P := fun t q => g (T (q, t)) ∈ U) (by
        intro q _
        have hchart : ContinuousAt T (q, c) := T.continuousAt (hs q)
        have hswap : ContinuousAt (Prod.swap : Real × S1 → S1 × Real) (c, q) :=
          continuous_swap.continuousAt
        have hc : ContinuousAt (fun z : Real × S1 => g (T (z.2, z.1))) (c, q) :=
          hg.continuousAt.comp (hchart.comp (f := Prod.swap) hswap)
        exact hc (hU.mem_nhds (hcU q)))
    simpa only [mem_univ, forall_const] using hh
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  rintro y ⟨_, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩
  apply hδsub (show t ∈ ball c δ from ?_) q
  rw [mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

namespace SphereSurgeryCoreCap.LowerAnnularEnd

variable {v : E3} {g : S2 → E3} {B : Set Real}
  {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}

theorem exists_physical_terminal_collar_in (A : LowerAnnularEnd D C h a b)
    (hg : Continuous g) (haD : a ≤ D.center)
    {c : Real} (hDc : D.center < c) (hcb : c < b)
    {U : Set E3} (hU : IsOpen U) (hEU : g '' A.cappedRegion c ⊆ U) :
    ∃ ε : Real, 0 < ε ∧ Icc (c - ε) (c + ε) ⊆ Ioo D.center b ∧
      A.chart '' (univ ×ˢ Icc (c - ε) (c + ε)) ⊆ _root_.interior C ∧
      g '' (A.chart '' (univ ×ˢ Icc (c - ε) (c + ε))) ⊆ U ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) →
        inner Real v (g (A.chart (q, t))) = t := by
  obtain ⟨δ, hδ, hδsub⟩ := Saddle.Caps.exists_terminal_collar_in A.chart hg
    (fun q => A.mem_source_of_mem_height_interval haD q ⟨hDc.le, hcb.le⟩) hU
    (fun q => hEU (mem_image_of_mem g (A.terminal_subset_cappedRegion hDc.le (mem_range_self q))))
  obtain ⟨ε₀, hε₀, hinterval, hret, hheight⟩ :=
    A.exists_physical_terminal_collar hDc hcb
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have hsmall : Icc (c - ε) (c + ε) ⊆ Icc (c - ε₀) (c + ε₀) := by
    intro t ht
    have he := min_le_left ε₀ δ
    constructor <;> dsimp [ε] at ht <;> linarith [ht.1, ht.2]
  have hsmallU : Icc (c - ε) (c + ε) ⊆ Icc (c - δ) (c + δ) := by
    intro t ht
    have he := min_le_right ε₀ δ
    constructor <;> dsimp [ε] at ht <;> linarith [ht.1, ht.2]
  refine ⟨ε, hε, hsmall.trans hinterval,
    (image_mono (prod_mono Subset.rfl hsmall)).trans hret,
    (image_mono (image_mono (prod_mono Subset.rfl hsmallU))).trans hδsub,
    fun q t ht => hheight q t (hsmall ht)⟩

end SphereSurgeryCoreCap.LowerAnnularEnd
end Poincare.Manifold.Schoenflies
