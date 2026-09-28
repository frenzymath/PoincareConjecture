import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalHeight

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

theorem exists_equal_physical_slices_of_surface_germ
    {s t : S2 → E3} (hs : Topology.IsEmbedding s) (ht : Topology.IsEmbedding t)
    (A B : OpenPartialHomeomorph (S1 × Real) S2) (height : E3 → Real)
    {b ε : Real} (hε : 0 < ε)
    (hAs : univ ×ˢ Icc (b - ε) (b + ε) ⊆ A.source)
    (hBs : univ ×ˢ Icc (b - ε) (b + ε) ⊆ B.source)
    (hAh : ∀ q z, z ∈ Icc (b - ε) (b + ε) → height (s (A (q, z))) = z)
    (hBh : ∀ q z, z ∈ Icc (b - ε) (b + ε) → height (t (B (q, z))) = z)
    (hrim : range (fun q : S1 => s (A (q, b))) =
      range (fun q : S1 => t (B (q, b))))
    {U : Set E3} (hU : IsOpen U)
    (hrimU : range (fun q : S1 => s (A (q, b))) ⊆ U)
    (hgerm : range s ∩ U = range t ∩ U) :
    ∃ δ : Real, 0 < δ ∧ δ < ε ∧
      ∀ z ∈ Icc (b - δ) (b + δ),
        range (fun q : S1 => s (A (q, z))) =
          range (fun q : S1 => t (B (q, z))) := by
  let V : Set (S1 × Real) := univ ×ˢ Ioo (b - ε) (b + ε)
  have hV : IsOpen V := isOpen_univ.prod isOpen_Ioo
  have hVA : V ⊆ A.source := fun x hx => hAs ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  have hVB : V ⊆ B.source := fun x hx => hBs ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  obtain ⟨Ua, hUa, heqa⟩ := hs.isInducing.isOpen_iff.mp
    (A.isOpen_image_of_subset_source hV hVA)
  obtain ⟨Ub, hUb, heqb⟩ := ht.isInducing.isOpen_iff.mp
    (B.isOpen_image_of_subset_source hV hVB)
  let W := U ∩ Ua ∩ Ub
  have hW : IsOpen W := (hU.inter hUa).inter hUb
  have hbase (q : S1) : (q, b) ∈ V := ⟨mem_univ _, by linarith, by linarith⟩
  have hWa (q : S1) : s (A (q, b)) ∈ W := by
    refine ⟨⟨hrimU (mem_range_self q), ?_⟩, ?_⟩
    · change A (q, b) ∈ s ⁻¹' Ua
      rw [heqa]
      exact mem_image_of_mem A (hbase q)
    · obtain ⟨q', hq'⟩ := hrim ▸ mem_range_self q
      rw [← hq']
      change B (q', b) ∈ t ⁻¹' Ub
      rw [heqb]
      exact mem_image_of_mem B (hbase q')
  have hWb (q : S1) : t (B (q, b)) ∈ W := by
    obtain ⟨q', hq'⟩ := hrim.symm ▸ mem_range_self q
    rw [← hq']
    exact hWa q'
  have hnear : ∀ᶠ z in 𝓝 b, ∀ q : S1,
      s (A (q, z)) ∈ W ∧ t (B (q, z)) ∈ W := by
    have hh := (isCompact_univ : IsCompact (univ : Set S1)).eventually_forall_of_forall_eventually
      (x₀ := b) (P := fun z q => s (A (q, z)) ∈ W ∧ t (B (q, z)) ∈ W) (by
        intro q _
        have hswap : ContinuousAt (Prod.swap : Real × S1 → S1 × Real) (b, q) :=
          continuous_swap.continuousAt
        have hchartA : ContinuousAt (fun x : Real × S1 => A (x.2, x.1)) (b, q) :=
          (A.continuousAt (hVA (hbase q))).comp (f := Prod.swap) hswap
        have hchartB : ContinuousAt (fun x : Real × S1 => B (x.2, x.1)) (b, q) :=
          (B.continuousAt (hVB (hbase q))).comp (f := Prod.swap) hswap
        have hca : ContinuousAt (fun x : Real × S1 => s (A (x.2, x.1))) (b, q) :=
          hs.continuous.continuousAt.comp hchartA
        have hcb : ContinuousAt (fun x : Real × S1 => t (B (x.2, x.1))) (b, q) :=
          ht.continuous.continuousAt.comp hchartB
        have ha : ∀ᶠ x : Real × S1 in 𝓝 (b, q), s (A (x.2, x.1)) ∈ W :=
          hca.preimage_mem_nhds (hW.mem_nhds (hWa q))
        have hb : ∀ᶠ x : Real × S1 in 𝓝 (b, q), t (B (x.2, x.1)) ∈ W :=
          hcb.preimage_mem_nhds (hW.mem_nhds (hWb q))
        exact ha.and hb)
    simpa only [mem_univ, forall_const] using hh
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min r ε / 2
  have hδ : 0 < δ := half_pos (lt_min hr hε)
  have hδr : δ < r := by dsimp [δ]; linarith [min_le_left r ε]
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_right r ε]
  refine ⟨δ, hδ, hδε, ?_⟩
  intro z hz
  have hze : z ∈ Icc (b - ε) (b + ε) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hzr : z ∈ ball b r := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    have hw := (hrsub hzr q).1
    obtain ⟨p, hp⟩ := (hgerm ▸ (show s (A (q, z)) ∈ range s ∩ U from
      ⟨mem_range_self _, hw.1.1⟩)).1
    have hpB : p ∈ B '' V := by
      rw [← heqb]
      change t p ∈ Ub
      rw [hp]
      exact hw.2
    obtain ⟨⟨q', z'⟩, hz', rfl⟩ := hpB
    have hez : z' = z := by
      have hh := congrArg height hp
      rwa [hBh q' z' ⟨hz'.2.1.le, hz'.2.2.le⟩, hAh q z hze] at hh
    subst z'
    exact ⟨q', hp⟩
  · rintro ⟨q, rfl⟩
    have hw := (hrsub hzr q).2
    obtain ⟨p, hp⟩ := (hgerm.symm ▸ (show t (B (q, z)) ∈ range t ∩ U from
      ⟨mem_range_self _, hw.1.1⟩)).1
    have hpA : p ∈ A '' V := by
      rw [← heqa]
      change s p ∈ Ua
      rw [hp]
      exact hw.1.2
    obtain ⟨⟨q', z'⟩, hz', rfl⟩ := hpA
    have hez : z' = z := by
      have hh := congrArg height hp
      rwa [hAh q' z' ⟨hz'.2.1.le, hz'.2.2.le⟩, hBh q z hze] at hh
    subst z'
    exact ⟨q', hp⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
