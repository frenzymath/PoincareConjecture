import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.Collar
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Decomposition

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

theorem Saddle.Caps.exists_physical_height_interval_of_germ
    (T : OpenPartialHomeomorph (S1 × Real) S2) (h physical : S2 → Real)
    {c : Real} (hs : ∀ q : S1, (q, c) ∈ T.source)
    (hheight : ∀ q t, (q, t) ∈ T.source → h (T (q, t)) = t)
    (hgerm : ∀ q : S1, h =ᶠ[𝓝 (T (q, c))] physical) :
    ∃ ε : Real, 0 < ε ∧
      univ ×ˢ Icc (c - ε) (c + ε) ⊆ T.source ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) → physical (T (q, t)) = t := by
  have hnear : ∀ᶠ t in 𝓝 c, ∀ q : S1,
      (q, t) ∈ T.source ∧ h (T (q, t)) = physical (T (q, t)) := by
    have hh := (isCompact_univ : IsCompact (univ : Set S1)).eventually_forall_of_forall_eventually
      (x₀ := c) (P := fun t q =>
        (q, t) ∈ T.source ∧ h (T (q, t)) = physical (T (q, t))) (by
          intro q _
          have hswap : ContinuousAt (Prod.swap : Real × S1 → S1 × Real) (c, q) :=
            continuous_swap.continuousAt
          have hchart : ContinuousAt (fun z : Real × S1 => T (z.2, z.1)) (c, q) :=
            (T.continuousAt (hs q)).comp (f := Prod.swap) hswap
          have hsource : ∀ᶠ z : Real × S1 in 𝓝 (c, q), (z.2, z.1) ∈ T.source :=
            hswap.preimage_mem_nhds (T.open_source.mem_nhds (hs q))
          exact hsource.and (hchart.eventually (hgerm q)))
    simpa only [mem_univ, forall_const] using hh
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall {t : Real} (ht : t ∈ Icc (c - δ / 2) (c + δ / 2)) : t ∈ ball c δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
  · rintro ⟨q, t⟩ ⟨_, ht⟩
    exact (hδsub (hsmall ht) q).1
  · intro q t ht
    obtain ⟨hsource, heq⟩ := hδsub (hsmall ht) q
    exact heq.symm.trans (hheight q t hsource)

namespace SphereSurgeryCoreCap

variable {v : E3} {g : S2 → E3} {B : Set Real}
  {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}

theorem LowerAnnularEnd.exists_physical_height_at_terminal
    (A : LowerAnnularEnd D C h a b) (hab : a ≤ b) (hDb : D.center ≤ b)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ ε : Real, 0 < ε ∧
      univ ×ˢ Icc (b - ε) (b + ε) ⊆ A.chart.source ∧
      ∀ q t, t ∈ Icc (b - ε) (b + ε) → inner Real v (g (A.chart (q, t))) = t := by
  apply Saddle.Caps.exists_physical_height_interval_of_germ A.chart h
    (fun p => inner Real v (g p))
  · intro q
    rw [A.source]
    exact ⟨mem_univ _, by linarith [A.delta_pos], by linarith [A.delta_pos]⟩
  · intro q t ht
    exact A.height q t ((A.source ▸ ht).2)
  · intro q
    exact hgerm _ (A.retained (mem_image_of_mem A.chart ⟨mem_univ _, hDb, le_rfl⟩))

theorem UpperAnnularEnd.exists_physical_height_at_terminal
    (A : UpperAnnularEnd D C h a b) (hab : a ≤ b) (haD : a ≤ D.center)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ ε : Real, 0 < ε ∧
      univ ×ˢ Icc (a - ε) (a + ε) ⊆ A.chart.source ∧
      ∀ q t, t ∈ Icc (a - ε) (a + ε) → inner Real v (g (A.chart (q, t))) = t := by
  apply Saddle.Caps.exists_physical_height_interval_of_germ A.chart h
    (fun p => inner Real v (g p))
  · intro q
    rw [A.source]
    exact ⟨mem_univ _, by linarith [A.reflected.delta_pos],
      by linarith [A.reflected.delta_pos]⟩
  · intro q t ht
    exact A.height q t ((A.source ▸ ht).2)
  · intro q
    apply hgerm _ (A.retained ?_)
    rw [A.region_eq_image]
    exact mem_image_of_mem A.chart ⟨mem_univ _, le_rfl, haD⟩

theorem AnnularEndFamily.exists_lower_terminal_physical_height
    (ends : AnnularEndFamily v g B C) (D : SphereSurgeryCoreCap v g B)
    (hD : D ∈ ends.caps) (hDb : D.center < ends.lowerCut) :
    ∃ ε : Real, 0 < ε ∧
      univ ×ˢ Icc (ends.lowerCut - ε) (ends.lowerCut + ε) ⊆
        (ends.lower D hD hDb).chart.source ∧
      ∀ q t, t ∈ Icc (ends.lowerCut - ε) (ends.lowerCut + ε) →
        inner Real v (g ((ends.lower D hD hDb).chart (q, t))) = t :=
  (ends.lower D hD hDb).exists_physical_height_at_terminal ends.lower_lt.le hDb.le
    ends.height_germ

theorem AnnularEndFamily.exists_upper_terminal_physical_height
    (ends : AnnularEndFamily v g B C) (D : SphereSurgeryCoreCap v g B)
    (hD : D ∈ ends.caps) (haD : ends.upperCut < D.center) :
    ∃ ε : Real, 0 < ε ∧
      univ ×ˢ Icc (ends.upperCut - ε) (ends.upperCut + ε) ⊆
        (ends.upper D hD haD).chart.source ∧
      ∀ q t, t ∈ Icc (ends.upperCut - ε) (ends.upperCut + ε) →
        inner Real v (g ((ends.upper D hD haD).chart (q, t))) = t :=
  (ends.upper D hD haD).exists_physical_height_at_terminal ends.upper_lt.le haD.le
    ends.height_germ

end SphereSurgeryCoreCap
end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
