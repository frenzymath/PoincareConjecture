import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.TransitionCompactness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped ContDiff Topology

namespace PoincareConjecture.M47



theorem terminalCommonInterval_smooth_actual_coordinate_limits
    {d : ℕ} {U V : ℕ → Set (EuclideanSpace ℝ (Fin d))}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    {Aseq Bseq : ℕ → ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {A B : ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {f : ℕ → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (F : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hpoint : ∀ i x, x ∈ U i → Tendsto (fun k => f i k x) atTop (𝓝 (F i x)))
    (hAseq : ∀ i, LocallyEventuallyContDiff (U i) (Aseq i))
    (hBseq : ∀ i, LocallyEventuallyContDiff (V i) (Bseq i))
    (hf : ∀ i, LocallyEventuallyContDiff (U i) (f i))
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (U i))
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (V i))
    (hAsymm : ∀ i k x, x ∈ U i → ∀ v w, Aseq i k x v w = Aseq i k x w v)
    (hBsymm : ∀ i k x, x ∈ V i → ∀ v w, Bseq i k x v w = Bseq i k x w v)
    (hApos : ∀ i x, x ∈ U i → ∀ v, v ≠ 0 → 0 < A i x v v)
    (hBpos : ∀ i x, x ∈ V i → ∀ v, v ≠ 0 → 0 < B i x v v)
    (hAlim : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Aseq i k)) (iteratedFDeriv ℝ m (A i)) atTop K)
    (hBlim : ∀ i m K, IsCompact K → K ⊆ V i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Bseq i k)) (iteratedFDeriv ℝ m (B i)) atTop K)
    (htarget : ∀ i K, IsCompact K → K ⊆ U i → ∃ L,
      IsCompact L ∧ L ⊆ V i ∧ ∀ᶠ k in atTop, MapsTo (f i k) K L)
    (hmetric : ∀ i K, IsCompact K → K ⊆ U i → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v w,
        Bseq i k (f i k x) (fderiv ℝ (f i k) x v) (fderiv ℝ (f i k) x w) =
          Aseq i k x v w) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      (∀ i, ContDiffOn ℝ ∞ (F i) (U i)) ∧
      (∀ i, MapsTo (F i) (U i) (V i)) ∧
      (∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f i (sigma k)))
        (iteratedFDeriv ℝ m (F i)) atTop K) ∧
      ∀ i x, x ∈ U i → ∀ v w,
        B i (F i x) (fderiv ℝ (F i) x v) (fderiv ℝ (F i) x w) = A i x v w := by
  obtain ⟨sigma, hsigma, f0, hsmooth, hmap, hjet, hinner⟩ :=
    CoordinateTransition.exists_common_smooth_isometry_limit_of_metric_convergence
      hU hV hAseq hBseq hf hA hB hAsymm hBsymm hApos hBpos hAlim hBlim
      htarget hmetric
  have heq (i : ℕ) : EqOn (f0 i) (F i) (U i) := by
    intro x hx
    have hzero := CoordinateTransition.locallyUniformly_of_tendsto_zeroJet
      (hU i) (hjet i 0)
    exact tendsto_nhds_unique (hzero.tendsto_at hx)
      ((hpoint i x hx).comp hsigma.tendsto_atTop)
  have hgerm (i : ℕ) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ U i) :
      f0 i =ᶠ[𝓝 x] F i := (heq i).eventuallyEq_of_mem ((hU i).mem_nhds hx)
  refine ⟨sigma, hsigma, fun i => (hsmooth i).congr (heq i).symm, ?_, ?_, ?_⟩
  · intro i x hx
    rw [← heq i hx]
    exact hmap i hx
  · intro i m K hK hKU
    apply (hjet i m K hK hKU).congr_right
    intro x hx
    exact ((hgerm i x (hKU hx)).iteratedFDeriv ℝ m).self_of_nhds
  · intro i x hx v w
    have hid := hinner i x hx v w
    rwa [heq i hx, (hgerm i x hx).fderiv_eq] at hid

end PoincareConjecture.M47
