import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.LowerContacts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.Barrier.Subsolution
noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

open Barrier

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem positive_at_chart_endpoint
    {D : Set M} (hD : IsCompact D) (α : M)
    (hchart : D ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) α).source)
    {g : ℝ → RiemannianMetric n M}
    (conn : ∀ t, LeviCivitaData (g t)) {a b : ℝ} (hab : a < b)
    {rho lam Lam H₀ ε : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH₀ : 0 ≤ H₀) (hε : 0 < ε)
    {gamma : ℝ → EuclideanSpace ℝ (Fin n)} (hg : ContDiff ℝ ∞ gamma)
    {v : M → ℝ → ℝ}
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (D ×ˢ Icc a b))
    (hvs : HeatLowerContacts conn (interior D) (Ioo a b) v)
    (hbounds : ∀ x ∈ interior D, ∀ t ∈ Ioo a b,
      0 < ballGap rho (gamma t) (extChartAt (𝓡 n) α x) →
        lam * ‖extChartAt (𝓡 n) α x - gamma t‖ ^ 2 ≤
            radialQuadratic (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t) ∧
          radialQuadratic (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t) ≤
            Lam * ‖extChartAt (𝓡 n) α x - gamma t‖ ^ 2 ∧
          radialTrace (g t) α (extChartAt (𝓡 n) α x) +
            radialDrift (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t) +
            ⟪extChartAt (𝓡 n) α x - gamma t, deriv gamma t⟫_ℝ ≤ H₀)
    (hinit : ∀ x ∈ D, 0 ≤ v x a)
    (hseed : ∀ x ∈ D, ‖extChartAt (𝓡 n) α x - gamma a‖ < rho → ε ≤ v x a)
    (hlateral : ∀ x ∈ D, x ∉ interior D → ∀ t ∈ Icc a b, 0 ≤ v x t)
    (hsupport : ∀ x ∈ D, x ∉ interior D → ∀ t ∈ Icc a b,
      rho ≤ ‖extChartAt (𝓡 n) α x - gamma t‖)
    {q : M} (hq : q ∈ D) (hend : extChartAt (𝓡 n) α q = gamma b) :
    0 < v q b := by
  let C := dampingConstant rho lam Lam H₀
  let w := chartBump α rho C a gamma
  have hgd : ∀ t, HasDerivAt gamma (deriv gamma t) t := fun t =>
    ((hg.differentiable (by simp)).differentiableAt (x := t)).hasDerivAt
  have hcoord : ContinuousOn (fun z : M × ℝ => (z.2, extChartAt (𝓡 n) α z.1))
      (D ×ˢ Icc a b) := by
    apply ContinuousOn.prodMk continuous_snd.continuousOn
    exact (continuousOn_extChartAt α).comp continuous_fst.continuousOn
      (fun z hz => by simpa only [extChartAt_source] using hchart hz.1)
  have hw : ContinuousOn (fun z : M × ℝ => w z.1 z.2) (D ×ˢ Icc a b) :=
    (contDiff_movingBump rho C a hg).continuous.comp_continuousOn hcoord
  have hws : ∀ t, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => w x t) (interior D) :=
    fun t => (contMDiffOn_chartBump α rho C a gamma t).mono
      (interior_subset.trans hchart)
  have hwd : ∀ x t, HasDerivAt (w x)
      (timeJet rho C a gamma t (extChartAt (𝓡 n) α x) (deriv gamma t)) t :=
    fun x t => hasDerivAt_chartBump α rho C a (hgd t) x
  have hcompare := comparison_on_Icc hD conn hab
    (u := fun x t => ε * w x t)
    (ut := fun x t => ε * timeJet rho C a gamma t (extChartAt (𝓡 n) α x) (deriv gamma t))
    (continuousOn_const.mul hw) hv
    (fun t _ => contMDiffOn_const.mul (hws t))
    (fun x _ t _ => (hwd x t).const_mul ε)
    (fun x hx t ht => by
      rw [(conn t).laplacian_const_mul]
      have h := chartBump_subsolution conn α a hrho hlam hLam hH₀
        (hgd t) (hchart (interior_subset hx)) (hbounds x hx t ht)
      rw [(hwd x t).deriv] at h
      exact mul_le_mul_of_nonneg_left h hε.le)
    hvs
    (fun x hx => by
      by_cases hdist : ‖extChartAt (𝓡 n) α x - gamma a‖ < rho
      · have hwle : w x a ≤ 1 := by
          simpa [w, chartBump, movingBump] using
            profile_le_one (ballGap rho (gamma a) (extChartAt (𝓡 n) α x))
        exact (mul_le_of_le_one_right hε.le hwle).trans (hseed x hx hdist)
      · have hz : w x a = 0 := movingBump_eq_zero C a gamma a hrho.le (le_of_not_gt hdist)
        simpa only [hz, mul_zero] using hinit x hx)
    (fun x hx hn t ht => by
      have hz : w x t = 0 := movingBump_eq_zero C a gamma t hrho.le (hsupport x hx hn t ht)
      simpa only [hz, mul_zero] using hlateral x hx hn t ht)
  have hpos : 0 < ε * w q b := by
    apply mul_pos hε
    change 0 < movingBump rho C a gamma b (extChartAt (𝓡 n) α q)
    rw [hend]
    exact movingBump_center_pos C a gamma b hrho
  exact hpos.trans_le (hcompare q hq b ⟨hab.le, le_rfl⟩)

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
