import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingCoordinates
import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingBlend

set_option autoImplicit false

open Function Set Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.M40

section SourceTranslation

variable {X E V : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem chartTranslation_lipschitzOn
    (e : OpenPartialHomeomorph X E) (A : E ≃L[ℝ] V)
    {s : Set X} {W : Set V} {C : ℝ≥0} (t : E)
    (hforward : LipschitzOnWith C (fun x => A (e x)) s)
    (hinverse : LipschitzOnWith C (fun v => e.symm (A.symm v)) W)
    (hshift : ∀ x ∈ s, A (e x - t) ∈ W) :
    LipschitzOnWith (C * C) (fun x => e.symm (e x - t)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  calc
    dist (e.symm (e x - t)) (e.symm (e y - t))
        = dist (e.symm (A.symm (A (e x - t))))
            (e.symm (A.symm (A (e y - t)))) := by simp
    _ ≤ (C : ℝ) * dist (A (e x - t)) (A (e y - t)) :=
      hinverse.dist_le_mul _ (hshift x hx) _ (hshift y hy)
    _ = (C : ℝ) * dist (A (e x)) (A (e y)) := by
      rw [map_sub, map_sub, dist_sub_right]
    _ ≤ (C : ℝ) * ((C : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hforward.dist_le_mul x hx y hy) C.coe_nonneg
    _ = (C * C : ℝ≥0) * dist x y := by simp [mul_assoc]

end SourceTranslation

section TranslatedMap

variable {X N E F V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem chartCoordinates_translated_dist_le
    (e : OpenPartialHomeomorph X E) (h : N → F) (B : F →L[ℝ] V)
    {q : X → N} {f : E → F} {s : Set X} {W : Set N}
    {C K D : ℝ≥0} {r : ℝ}
    (hq : LipschitzWith K q)
    (htarget : LipschitzOnWith C (fun y => B (h y)) W)
    (htranslation : ∀ t ∈ ball (0 : E) r,
      LipschitzOnWith D (fun x => e.symm (e x - t)) s)
    (himage : ∀ x ∈ s, ∀ t ∈ ball (0 : E) r, q (e.symm (e x - t)) ∈ W)
    (hext : ∀ x ∈ s, ∀ t ∈ ball (0 : E) r,
      f (e x - t) = h (q (e.symm (e x - t)))) :
    ∀ x ∈ s, ∀ y ∈ s, ∀ t ∈ ball (0 : E) r,
      dist (B (f (e x - t))) (B (f (e y - t))) ≤
        (C * K * D : ℝ≥0) * dist x y := by
  intro x hx y hy t ht
  rw [hext x hx t ht, hext y hy t ht]
  calc
    dist (B (h (q (e.symm (e x - t))))) (B (h (q (e.symm (e y - t)))))
        ≤ (C : ℝ) * dist (q (e.symm (e x - t))) (q (e.symm (e y - t))) :=
      htarget.dist_le_mul _ (himage x hx t ht) _ (himage y hy t ht)
    _ ≤ (C : ℝ) * ((K : ℝ) * dist (e.symm (e x - t)) (e.symm (e y - t))) :=
      mul_le_mul_of_nonneg_left (hq.dist_le_mul _ _) C.coe_nonneg
    _ ≤ (C : ℝ) * ((K : ℝ) * ((D : ℝ) * dist x y)) := by
      apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
      exact mul_le_mul_of_nonneg_left
        ((htranslation t ht).dist_le_mul x hx y hy) K.coe_nonneg
    _ = (C * K * D : ℝ≥0) * dist x y := by simp [mul_assoc]

end TranslatedMap

section TargetBlend

variable {X N E F V : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem chartConvolutionBlend_lipschitzOn
    (h : OpenPartialHomeomorph N F) (B : F ≃L[ℝ] V)
    (φ : ContDiffBump (0 : E)) (a : X → E)
    {f : E → F} {q : X → F} {ρ : X → ℝ} {s : Set X} {W : Set V}
    {L A δ C : ℝ≥0}
    (hf : LocallyIntegrable f μ)
    (hq : ∀ x ∈ s, q x = f (a x))
    (hbound : ∀ x ∈ s, ∀ y ∈ s, ∀ t ∈ ball (0 : E) φ.rOut,
      dist (B (f (a x - t))) (B (f (a y - t))) ≤ (L : ℝ) * dist x y)
    (hρ : LipschitzOnWith A ρ s) (hρrange : ∀ x ∈ s, ρ x ∈ Icc 0 1)
    (hclose : ∀ x ∈ s,
      dist (B (normalizedConvolution μ φ f (a x))) (B (q x)) ≤ δ)
    (hinverse : LipschitzOnWith C (fun v => h.symm (B.symm v)) W)
    (hrange : ∀ x ∈ s,
      B (cutoffBlend ρ q (fun y => normalizedConvolution μ φ f (a y)) x) ∈ W) :
    LipschitzOnWith (C * (L + A * δ))
      (fun x => h.symm
        (cutoffBlend ρ q (fun y => normalizedConvolution μ φ f (a y)) x)) s := by
  have hqLip : LipschitzOnWith L (fun x => B (q x)) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [sub_zero, ← hq x hx, ← hq y hy] using
      hbound x hx y hy 0 (mem_ball_self φ.rOut_pos)
  have hgLip : LipschitzOnWith L
      (fun x => B (normalizedConvolution μ φ f (a x))) s :=
    normalizedConvolution_lipschitzOn_of_translated_bound
      φ a B.toContinuousLinearMap hf hbound
  have hblend := cutoffBlend_lipschitzOn hρ hρrange hqLip hgLip hclose
  have hmap (x : X) :
      B (cutoffBlend ρ q (fun y => normalizedConvolution μ φ f (a y)) x) =
        cutoffBlend ρ (fun y => B (q y))
          (fun y => B (normalizedConvolution μ φ f (a y))) x := by
    simp only [cutoffBlend, map_add, map_smul]
  have hmaps : MapsTo
      (cutoffBlend ρ (fun y => B (q y))
        (fun y => B (normalizedConvolution μ φ f (a y)))) s W := by
    intro x hx
    rw [← hmap]
    exact hrange x hx
  have hc := hinverse.comp hblend hmaps
  intro x hx y hy
  simpa only [Function.comp_apply, ← hmap, B.symm_apply_apply] using hc hx hy

end TargetBlend

end PoincareConjecture.M40
