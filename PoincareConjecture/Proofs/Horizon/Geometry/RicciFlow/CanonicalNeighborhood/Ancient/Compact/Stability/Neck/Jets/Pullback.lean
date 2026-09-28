import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Comparison.Jets.ComparisonCoordinateJets
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.TerminalNeck

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem eventually_small_bilinearPullback_jets_at_filter
    {κ : Type*} {l : Filter κ}
    {ι : Type*} {f : ι → E → E} (x : ι → E) {K : Set E}
    {B : κ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hmap : ∀ i, f i (x i) ∈ K)
    (hBs : ∀ᶠ k in l, ∀ y ∈ K, ContDiffAt ℝ ∞ (B k) y)
    (m : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hfj : ∀ i j, 1 ≤ j → j ≤ m + 1 →
      ‖iteratedFDeriv ℝ j (f i) (x i)‖ ≤ C)
    (hBj : ∀ η : ℝ, 0 < η → ∀ᶠ k in l, ∀ y ∈ K, ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j (B k) y‖ ≤ η)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in l, ∀ i j, j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y => (B k (f i y)).bilinearComp
        (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) (x i)‖ ≤ η := by
  let D : ℝ := 2 ^ m * 2 ^ m * m.factorial * C ^ m * C * C
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hD : 0 < D := by dsimp [D]; positivity
  have hηD : 0 < η / D := div_pos hη hD
  filter_upwards [hBs, hBj (η / D) hηD] with k hks hkj i j hj
  apply (MetricSurgery.norm_iteratedFDeriv_bilinearPullback_at
    (hf i) (hks _ (hmap i)) j hηD.le hC
    (fun l hl => hkj _ (hmap i) l (hl.trans hj))
    (fun l hl hl' => hfj i l hl (by omega))).trans
  calc
    (2 ^ j * 2 ^ j * j.factorial * C ^ j * C * C) * (η / D) ≤ D * (η / D) := by
      dsimp [D]
      gcongr
      all_goals norm_num
    _ = η := mul_div_cancel₀ η hD.ne'


theorem eventually_small_bilinearPullback_jets_at
    {ι : Type*} {f : ι → E → E} (x : ι → E) {K : Set E}
    {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hmap : ∀ i, f i (x i) ∈ K)
    (hBs : ∀ᶠ k in atTop, ∀ y ∈ K, ContDiffAt ℝ ∞ (B k) y)
    (m : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hfj : ∀ i j, 1 ≤ j → j ≤ m + 1 →
      ‖iteratedFDeriv ℝ j (f i) (x i)‖ ≤ C)
    (hBj : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ y ∈ K, ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j (B k) y‖ ≤ η)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ i j, j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y => (B k (f i y)).bilinearComp
        (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) (x i)‖ ≤ η :=
  eventually_small_bilinearPullback_jets_at_filter x hf hmap hBs m hC hfj hBj hη



theorem eventually_small_bilinearPullback_jets_of_compact_convergence
    {ι : Type*} {f : ι → E → E} (x : ι → E) {U K : Set E}
    {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hmap : ∀ i, f i (x i) ∈ K)
    (hlocal : ∀ y ∈ U, ∃ W, IsOpen W ∧ y ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) W)
    (m : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hfj : ∀ i j, 1 ≤ j → j ≤ m + 1 →
      ‖iteratedFDeriv ℝ j (f i) (x i)‖ ≤ C)
    (hBj : ∀ j, j ≤ m → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j (B k)) (fun _ => 0) atTop K)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ i j, j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y => (B k (f i y)).bilinearComp
        (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) (x i)‖ ≤ η := by
  apply eventually_small_bilinearPullback_jets_at x hf hmap
    (Poincare.Analysis.Calculus.eventually_contDiffAt_on_compact hK hKU hlocal)
    m hC hfj ?_ hη
  intro δ hδ
  have he : ∀ᶠ k in atTop, ∀ j ∈ Iic m, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ j (B k) y‖ ≤ δ := by
    apply (eventually_all_finite (finite_Iic m)).mpr
    intro j hj
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hBj j hj) δ hδ] with k hk y hy
    simpa only [dist_zero_left] using (hk y hy).le
  exact he.mono fun k hk y hy j hj => hk j hj y hy

end PoincareConjecture.TerminalNeck
