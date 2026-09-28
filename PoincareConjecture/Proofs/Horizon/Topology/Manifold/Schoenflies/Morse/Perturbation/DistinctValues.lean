import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Perturbation.SingleCritical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Restriction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_ambient_distinct_values_of_finite_morse_height
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v : S2)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0}.Finite)
    (hcoordinates : ∀ p : S2, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0 ->
      ∃ (e : OpenPartialHomeomorph E2 S2) (σ : Fin 2 -> Real),
        (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        ∀ x ∈ e.source, inner Real (v : E3) (f (e x)) =
          inner Real (v : E3) (f p) + ∑ i : Fin 2, σ i * x i ^ 2)
    {ε : Real} (hε : 0 < ε) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, D y = y) ∧
      (∀ p : S2, mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : E3) (D (f q))) p = 0 ↔
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (v : E3) (f q)) p = 0) ∧
      InjOn (fun p => inner Real (v : E3) (D (f p)))
        {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : E3) (f q)) p = 0} ∧
      (∀ p : S2, mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : E3) (f q)) p = 0 ->
        |inner Real (v : E3) (D (f p)) - inner Real (v : E3) (f p)| < ε) ∧
      ∀ p : S2, mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : E3) (f q)) p = 0 ->
        (fun q => inner Real (v : E3) (D (f q))) =ᶠ[𝓝 p]
          (fun q => inner Real (v : E3) (f q) +
            (inner Real (v : E3) (D (f p)) - inner Real (v : E3) (f p))) := by
  classical
  let h : S2 -> Real := fun p => inner Real (v : E3) (f p)
  let H (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) : S2 -> Real :=
    fun p => inner Real (v : E3) (D (f p))
  let C : Set S2 := {p | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}
  have haux : ∀ S : Set S2, S.Finite -> S ⊆ C ->
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, D y = y) ∧
        (∀ p : S2, mfderiv (𝓡 2) 𝓘(Real, Real) (H D) p = 0 ↔
          mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0) ∧
        InjOn (H D) S ∧ (∀ q ∈ C, |H D q - h q| < ε) ∧
        (∀ q ∈ C, q ∉ S -> H D q = h q) ∧
        ∀ q ∈ C, H D =ᶠ[𝓝 q] (fun x => h x + (H D q - h q)) := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty =>
      intro _
      refine ⟨Diffeomorph.refl (𝓡 3) E3 ∞,
        ⟨∅, isCompact_empty, fun _ _ => rfl⟩,
        fun _ => Iff.rfl, injOn_empty _, ?_, fun _ _ _ => rfl, ?_⟩
      · intro q _
        simpa [H, h] using hε
      · intro q _
        exact Eventually.of_forall (by simp [H, h])
    | @insert p S hpS hS ih =>
      intro hSC
      have hpC : p ∈ C := hSC (mem_insert p S)
      have hSC' : S ⊆ C := (subset_insert p S).trans hSC
      obtain ⟨D, hDc, hcritical, hinj, hsmall, hfixed, hgerm⟩ := ih hSC'
      have hDf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
          (fun q => D (f q)) := hf.comp_localDiffeomorph D.isLocalDiffeomorph
            (D.injective.comp hf.isEmbedding.injective)
      have hDcoordinates := morse_coordinates_of_eventuallyEq_add_const_at_critical_points
        hcoordinates (fun q hq => (hcritical q).mp hq)
        (fun q hq => ⟨H D q - h q, hgerm q ((hcritical q).mp hq)⟩)
      have hpD : mfderiv (𝓡 2) 𝓘(Real, Real) (H D) p = 0 := (hcritical p).mpr hpC
      obtain ⟨e, σ, hσ, he0, hep, he, hei, hform⟩ := hDcoordinates p hpD
      obtain ⟨L, a, Phi, hL, ha, havoid, _, _, hPhifix, hPhicrit, hPhip, hPhiother⟩ :=
        exists_ambient_shift_of_morse_critical_point hDf v p hpD
          e he0 hep he hei σ hσ hform hε (hS.image (H D))
      let D' := D.trans (Phi 1)
      have hpoint : H D' =ᶠ[𝓝 p] (fun q => H D q + a) := by
        simpa [H, D'] using hPhip 1
      have hother (q : S2) (hq : q ∈ C) (hqp : q ≠ p) :
          H D' =ᶠ[𝓝 q] H D := hPhiother q ((hcritical q).mpr hq) hqp 1
      have heq (q : S2) (hq : q ∈ C) (hqp : q ≠ p) : H D' q = H D q :=
        (hother q hq hqp).eq_of_nhds
      have heqS (q : S2) (hq : q ∈ S) : H D' q = H D q :=
        heq q (hSC' hq) (fun heq => hpS (heq ▸ hq))
      have hpointvalue : H D' p = H D p + a := hpoint.eq_of_nhds
      refine ⟨D', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨K, hK, hKfix⟩ := hDc
        refine ⟨K ∪ L, hK.union hL, fun y hy => ?_⟩
        change Phi 1 (D y) = y
        rw [hKfix y (fun hyK => hy (Or.inl hyK)), hPhifix 1 y (fun hyL => hy (Or.inr hyL))]
      · intro q
        exact (hPhicrit 1 q).trans (hcritical q)
      · apply (injOn_insert hpS).mpr
        constructor
        · intro x hx y hy hxy
          exact hinj hx hy (by simpa only [heqS x hx, heqS y hy] using hxy)
        · rintro ⟨q, hq, hqp⟩
          apply havoid
          refine ⟨q, hq, ?_⟩
          exact (heqS q hq).symm.trans (hqp.trans hpointvalue)
      · intro q hq
        by_cases hqp : q = p
        · subst q
          simpa only [hpointvalue, hfixed p hpC hpS, add_sub_cancel_left] using ha
        · simpa only [heq q hq hqp] using hsmall q hq
      · intro q hq hqS
        have hqp : q ≠ p := fun heq => hqS (Or.inl heq)
        exact (heq q hq hqp).trans (hfixed q hq (fun hqS' => hqS (Or.inr hqS')))
      · intro q hq
        by_cases hqp : q = p
        · subst q
          filter_upwards [hpoint, hgerm p hpC] with x hx hx'
          rw [hx, hx', hpointvalue]
          ring
        · filter_upwards [hother q hq hqp, hgerm q hq] with x hx hx'
          rw [hx, hx', heq q hq hqp]
  obtain ⟨D, hDc, hcritical, hinj, hsmall, _, hgerm⟩ := haux C hfinite subset_rfl
  exact ⟨D, hDc, hcritical, hinj, hsmall, hgerm⟩

theorem exists_morse_height_with_distinct_critical_values
    (f : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> EuclideanSpace Real (Fin 3))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {ε : Real} (hε : 0 < ε) :
    ∃ (v : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (D : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace Real (Fin 3)) (EuclideanSpace Real (Fin 3)) ∞),
      (∃ K : Set (EuclideanSpace Real (Fin 3)), IsCompact K ∧
        ∀ y ∉ K, D y = y) ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p => D (f p)) ∧
      {p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 |
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (f q)) p = 0}.Finite ∧
      (∀ p : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (D (f q))) p = 0 ↔
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (f q)) p = 0) ∧
      InjOn (fun p => inner Real (v : EuclideanSpace Real (Fin 3)) (D (f p)))
        {p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 |
          mfderiv (𝓡 2) 𝓘(Real, Real)
            (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (f q)) p = 0} ∧
      (∀ p : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (f q)) p = 0 ->
        |inner Real (v : EuclideanSpace Real (Fin 3)) (D (f p)) -
          inner Real (v : EuclideanSpace Real (Fin 3)) (f p)| < ε) ∧
      ∀ p : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (D (f q))) p = 0 ->
        ∃ (e : OpenPartialHomeomorph (EuclideanSpace Real (Fin 2))
            (sphere (0 : EuclideanSpace Real (Fin 3)) 1)) (σ : Fin 2 -> Real),
          (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          ∀ x ∈ e.source,
            inner Real (v : EuclideanSpace Real (Fin 3)) (D (f (e x))) =
              inner Real (v : EuclideanSpace Real (Fin 3)) (D (f p)) +
                ∑ i : Fin 2, σ i * x i ^ 2 := by
  obtain ⟨v, hfinite, hcoordinates⟩ := exists_morse_height f hf
  obtain ⟨D, hDc, hcritical, hinj, hsmall, hgerm⟩ :=
    exists_ambient_distinct_values_of_finite_morse_height hf v hfinite hcoordinates hε
  have hDf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun p => D (f p)) := hf.comp_localDiffeomorph D.isLocalDiffeomorph
        (D.injective.comp hf.isEmbedding.injective)
  refine ⟨v, D, hDc, hDf, hfinite, hcritical, hinj, hsmall, ?_⟩
  apply morse_coordinates_of_eventuallyEq_add_const_at_critical_points hcoordinates
    (fun p hp => (hcritical p).mp hp)
  intro p hp
  exact ⟨_, hgerm p ((hcritical p).mp hp)⟩

end Poincare.Manifold.Schoenflies
