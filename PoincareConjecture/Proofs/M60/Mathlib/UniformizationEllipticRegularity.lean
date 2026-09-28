import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Eigenfunction










set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M60

open Poincare.Analysis Poincare.Analysis.Elliptic
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean

private theorem smooth_memWkpLocally {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) {O : Set (EuclideanSpace ℝ (Fin n))}
    (hO : IsOpen O) : MemWkpLocally k f O := by
  intro x hx
  obtain ⟨eta, heta, hetac, -, heta1, -⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff (isCompact_closedBall x 1)
      isOpen_univ (subset_univ _)
  let W := O ∩ Metric.ball x 1
  have hW : IsOpen W := hO.inter Metric.isOpen_ball
  refine ⟨W, hW, ⟨hx, Metric.mem_ball_self (by norm_num)⟩, inter_subset_left, ?_⟩
  have hreg := MemWkp_of_smooth_compactSupport isOpen_univ (heta.mul hf)
    hetac.mul_right (subset_univ _) (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
  apply (MemWkp_congr_ae (by norm_num) hW (v := f) ?_).mp
    (hreg.mono_set (by norm_num) hW (subset_univ _))
  filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
  change eta y * f y = f y
  rw [heta1 y (Metric.ball_subset_closedBall hy.2), one_mul]




theorem exists_smooth_representative_of_smooth_forcing
    {n : ℕ} (hn : 0 < n)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef) (hf : ContDiffOn ℝ ∞ f O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hpartial : ∀ i phi, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ O →
      (∫ x in O, u x * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
        -(∫ x in O, p i x * phi x))
    (heq : ∀ phi, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ phi x (EuclideanSpace.single i 1)) = ∫ x in O, f x * phi x) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] u := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply Sobolev.EuclideanIteratedEmbedding.exists_smooth_representative_of_memWkp_locally
  intro x hx k
  obtain ⟨V, hV, hxV, hVc, hVO, B, hBA, hBf⟩ :=
    exists_global_elliptic_extension hO (isCompact_singleton (x := x))
      (singleton_subset_iff.mpr hx) A f hA hpos hf
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
  have heqV : Iteration.WeakEquation V (Iteration.matrixFlux B.a p) B.c := by
    intro phi hphi hphic hphiV
    have he := weakEquation_congr_restrict hVO' hBA (fun _ _ _ => rfl) heq
      phi hphi hphic hphiV
    refine he.trans ?_
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    rw [hBf hy]
  have hreg := Iteration.memWkpLocally_add_two_of_weakEquation k hV B.smooth_a hposV
    huV hpV hwV (smooth_memWkpLocally B.smooth_c k hV) heqV
  obtain ⟨W, hW, hxW, hWV, huW⟩ := (hreg.mono_order (by omega : k ≤ k + 2)) x
    (hxV (mem_singleton x))
  exact ⟨W, hW, hxW, hWV.trans hVO', huW⟩

end PoincareConjecture.M60
