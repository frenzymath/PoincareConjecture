import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakVerticalSeparation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus














set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem observed_boundary_discrepancy_uniform_bound
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) :
    ∃ C : ℝ, 0 < C ∧ ∀ c0 c1 : ℝ → M,
      ContDiff ℝ 1 (fun x => e (c1 x) - e (c0 x)) →
      ∀ A : M64Annulus g c0 c1, ∀ r : ℝ, 0 < r →
        (∫ x in Icc (0 : ℝ) curvePeriod, ‖e (c1 x) - e (c0 x)‖ ^ 2) ≤
          C * r * m64ClassicalWeightedGramEnergy g A r := by
  obtain ⟨Q, K, hQ, -, hb, hpos, -, hgram⟩ :=
    m64ChartReadable_observed_metric g e he hread
  obtain ⟨D, -, hcoercive⟩ := m64ObservedMetric_tangent_coercivity g e he Q hgram
  have hD : 0 < max D 1 := lt_max_of_lt_right zero_lt_one
  let C := 2 * max D 1
  have hC : 0 < C := mul_pos (by norm_num) hD
  refine ⟨C, hC, ?_⟩
  intro c0 c1 hd A r hr
  obtain ⟨W, hmap, hcol⟩ := m64ObservedWeakAnnulus_of_annulus A e he
  have hWE := m64ObservedWeakAnnulus_seed_weightedEnergy_eq A e he Q
    (m64ObservedMetric_tangent_diagonal g e he Q hgram) W hmap hcol r
  have hvertical := W.weightedEnergy_ge_vertical_boundary Q hQ hei hb hpos hcoercive hd hr
  change (r⁻¹ / C) * (∫ x in Icc (0 : ℝ) curvePeriod, ‖e (c1 x) - e (c0 x)‖ ^ 2) ≤
    W.weightedEnergy Q r at hvertical
  have hh := mul_le_mul_of_nonneg_left hvertical (mul_nonneg hC.le hr.le)
  have heq (z : ℝ) : (C * r) * ((r⁻¹ / C) * z) = z := by
    field_simp [hr.ne', hC.ne']
  rw [heq, hWE] at hh
  exact hh




theorem free_annulus_boundary_discrepancy_tendsto_zero_of_modulus_collapse
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (hs0 : ∀ j, ContDiff ℝ 1 (sigma0 j).map)
    (hs1 : ∀ j, ContDiff ℝ 1 (sigma1 j).map)
    (A : ∀ j, M64Annulus g (c0 ∘ (sigma0 j).map) (c1 ∘ (sigma1 j).map))
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hcollapse : Tendsto r atTop (𝓝 0))
    {K : ℝ} (henergy : ∀ j, m64ClassicalWeightedGramEnergy g (A j) (r j) ≤ K) :
    Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
      ‖e (c1 ((sigma1 j).map x)) - e (c0 ((sigma0 j).map x))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := observed_boundary_discrepancy_uniform_bound g e he hei hread
  have hc0e : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hc1e : ContDiff ℝ 1 (e ∘ c1) := contMDiff_iff_contDiff.mp (he.comp hc1)
  have hupper (j : ℕ) : (∫ x in Icc (0 : ℝ) curvePeriod,
      ‖e (c1 ((sigma1 j).map x)) - e (c0 ((sigma0 j).map x))‖ ^ 2) ≤ C * r j * K := by
    have hd : ContDiff ℝ 1 (fun x => e ((c1 ∘ (sigma1 j).map) x) -
        e ((c0 ∘ (sigma0 j).map) x)) :=
      (hc1e.comp (hs1 j)).sub (hc0e.comp (hs0 j))
    exact (hbound _ _ hd (A j) (r j) (hr j)).trans
      (mul_le_mul_of_nonneg_left (henergy j) (mul_nonneg hC.le (hr j).le))
  have hlim : Tendsto (fun j => C * r j * K) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hcollapse).mul_const K
  exact squeeze_zero (fun j => integral_nonneg (fun _ => sq_nonneg _)) hupper hlim

end PoincareConjecture.M64
