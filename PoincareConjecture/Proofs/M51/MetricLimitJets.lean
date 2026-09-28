import PoincareConjecture.Proofs.M51.MetricJetCurvature
import PoincareConjecture.Proofs.M51.LimitPullback

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M51

variable {A : GeneralizedSliceCarrier.{u}}

theorem contDiffAt_singularMetricCoefficient
    (g : RiemannianMetric 3 A.carrier) (q : A.carrier) (a b : Fin 3)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    ContDiffAt ℝ ∞ (singularMetricCoefficient g q a b) p := by
  have hc := (g.contDiffOn_chartCoefficients q).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp)
  exact (hc.clm_apply contDiffAt_const).clm_apply contDiffAt_const

theorem metricLimit_jets_tendsto
    (g : ℝ → RiemannianMetric 3 A.carrier) (g₀ : RiemannianMetric 3 A.carrier)
    {T : ℝ} (hlim : SurgeryMetricLimitOn A A g g₀ id univ T)
    (q : A.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (htarget : K ⊆ (extChartAt (𝓡 3) q).target)
    {α : Type*} {l : Filter α} {t : α → ℝ} (ht : Tendsto t l (𝓝[<] T))
    {z : α → EuclideanSpace ℝ (Fin 3)}
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ K) (hz : Tendsto z l (𝓝[K] p))
    (k : ℕ) (a b : Fin 3) :
    Tendsto (fun i => iteratedFDeriv ℝ k (singularMetricCoefficient (g (t i)) q a b) (z i)) l
      (𝓝 (iteratedFDeriv ℝ k (singularMetricCoefficient g₀ q a b) p)) := by
  let J := fun s y => iteratedFDeriv ℝ k (singularMetricCoefficient (g s) q a b) y
  let J₀ := iteratedFDeriv ℝ k (singularMetricCoefficient g₀ q a b)
  have hcoeff : surgeryMetricCoefficient g₀
      (fun z => id ((extChartAt (𝓡 3) q).symm z)) a b =
      singularMetricCoefficient g₀ q a b := rfl
  have herror : Tendsto (fun i => J (t i) (z i) - J₀ (z i)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro eta heta
    obtain ⟨d, hd, hbound⟩ := hlim q (mem_univ q) K hK htarget
      (subset_univ _) k a b eta heta
    have htime : Ioo (T - d) T ∈ 𝓝[<] T :=
      (nhdsLT_basis T).mem_of_mem (by linarith)
    filter_upwards [ht htime, hz self_mem_nhdsWithin] with i hi hzi
    simpa only [dist_zero_right, J, J₀, hcoeff] using hbound (t i) hi.1 hi.2 (z i) hzi
  have htargetJet : Tendsto (fun i => J₀ (z i)) l (𝓝 (J₀ p)) :=
    ((contDiffAt_singularMetricCoefficient g₀ q a b (htarget hp)).continuousAt_iteratedFDeriv
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).continuousWithinAt.tendsto.comp hz
  have hsum := herror.add htargetJet
  simpa only [sub_add_cancel, zero_add] using hsum

end PoincareConjecture.M51
