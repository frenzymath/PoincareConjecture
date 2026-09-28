import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets
import Mathlib.Topology.UniformSpace.UniformConvergence











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology




theorem tendstoUniformlyOn_bilinear_jets_of_scalar_entries
    {ι A E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {l : Filter ι} {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V)
    {f : ι → A → E → V →L[ℝ] V →L[ℝ] ℝ}
    {g : A → E → V →L[ℝ] V →L[ℝ] ℝ} {K : Set (A × E)} (m : ℕ)
    (hf : ∀ᶠ k in l, ∀ p ∈ K, ContDiffAt ℝ ∞ (f k p.1) p.2)
    (hg : ∀ p ∈ K, ContDiffAt ℝ ∞ (g p.1) p.2)
    (hjet : ∀ i j : Fin n, TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (fun y => f k p.1 y (b i) (b j)) p.2)
      (fun p => iteratedFDeriv ℝ m (fun y => g p.1 y (b i) (b j)) p.2) l K) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (f k p.1) p.2)
      (fun p => iteratedFDeriv ℝ m (g p.1) p.2) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  let d : ℝ := 2 * ((n : ℝ) * n + 1)
  have hd : 0 < d := by dsimp only [d]; positivity
  have htol : 0 < delta / d := div_pos hdelta hd
  have hall := Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
    Metric.tendstoUniformlyOn_iff.mp (hjet i j) (delta / d) htol
  filter_upwards [hf, hall] with k hk hkj p hp
  have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hdiff := (hg p hp).sub (hk p hp)
  have hbound : ‖iteratedFDeriv ℝ m (g p.1 - f k p.1) p.2‖ ≤
      (n : ℝ) * n * (delta / d) := by
    apply PoincareConjecture.SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components
      b hdiff m
    intro i j
    have hgi : ContDiffAt ℝ ∞ (fun y => g p.1 y (b i) (b j)) p.2 :=
      ((hg p hp).clm_apply contDiffAt_const).clm_apply contDiffAt_const
    have hfi : ContDiffAt ℝ ∞ (fun y => f k p.1 y (b i) (b j)) p.2 :=
      ((hk p hp).clm_apply contDiffAt_const).clm_apply contDiffAt_const
    change ‖iteratedFDeriv ℝ m
      ((fun y => g p.1 y (b i) (b j)) - (fun y => f k p.1 y (b i) (b j))) p.2‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hgi.of_le hm) (hfi.of_le hm)]
    simpa only [dist_eq_norm] using (hkj i j p hp).le
  rw [dist_eq_norm, ← iteratedFDeriv_sub_apply ((hg p hp).of_le hm)
    ((hk p hp).of_le hm)]
  apply hbound.trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ hd]
  dsimp only [d]
  nlinarith [sq_nonneg (n : ℝ)]
