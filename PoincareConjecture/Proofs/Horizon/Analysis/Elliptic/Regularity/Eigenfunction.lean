import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.Bootstrap
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.SmoothRepresentative

open Set MeasureTheory
open scoped ContDiff

namespace Poincare.Analysis.Elliptic

theorem exists_smooth_representative
    {n : ℕ} (hn : 0 < n)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (c u : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hc : ContDiffOn ℝ ∞ c O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hpartial : ∀ i φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in O, p i x * φ x))
    (heq : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in O, c x * u x * φ x) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] u := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply Sobolev.EuclideanIteratedEmbedding.exists_smooth_representative_of_memWkp_locally
  intro x hx k
  obtain ⟨V, hV, hxV, hVc, hVO, B, hBA, hBc⟩ :=
    exists_global_elliptic_extension hO (isCompact_singleton (x := x))
      (singleton_subset_iff.mpr hx) A c hA hpos hc
  have hVO' : V ⊆ O := subset_closure.trans hVO
  have huV := (hu (closure V) hVc hVO).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)
  have hpV (i : Fin n) := (hp i (closure V) hVc hVO).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)
  have hwV (i : Fin n) : Sobolev.Weak.HasWeakPartialDeriv i (p i) u V :=
    (show Sobolev.Weak.HasWeakPartialDeriv i (p i) u O from hpartial i).restrict hV hVO'
  have hposV : ∀ y ∈ V, (B.a y).PosDef := by
    intro y hy
    rw [hBA hy]
    exact hpos y (hVO' hy)
  have heqV : Iteration.WeakEquation V (Iteration.matrixFlux B.a p)
      (fun y => B.c y * u y) := by
    intro φ hφ hφc hφV
    have he := weakEquation_congr_restrict hVO' hBA (fun _ _ _ => rfl) heq
      φ hφ hφc hφV
    calc
      _ = ∫ y in V, c y * u y * φ y := he
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
        rw [hBc hy]
  obtain ⟨W, hW, hxW, hWV, huW⟩ :=
    Iteration.memWkpLocally_all_of_weakEigenfunction hV B.smooth_a hposV B.smooth_c
      huV hpV hwV heqV k x (hxV (mem_singleton x))
  exact ⟨W, hW, hxW, hWV.trans hVO', huW⟩

end Poincare.Analysis.Elliptic
