import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerHarmonic
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerChartDecay
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerC1
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityRepresentative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Euler

theorem minimum_representative_contMDiffOn {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {U : Set LoopPlane} (hU : IsOpen U) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) (q : LoopPlane → M)
    (hqc : ContinuousOn q U) (hq : q =ᵐ[volume.restrict U] F.value) :
    ContMDiffOn (𝓡 2) (𝓡 3) 1 q U := by
  intro x hx
  obtain ⟨R, ε, hR, hε, _hRU, gE, DE, X, hX, hXc, _hsource, hcap, _hmetric,
    _hfield, hEq⟩ := exists_weak_harmonic_chart g e he hemb.injective hinj hU F hmin q hqc hq hx
  obtain ⟨s0, β, Λ, hs0, hβ, _hβ1, hΛ, _hsV, hdecay⟩ :=
    exists_chart_energy_decay g e he hinj hemb compact hU isOpen_ball F hmin X q hqc hq
      hx (mem_ball_self (show 0 < 8 * R by positivity)) (fun z _ => hX z)
  let s := min s0 R
  have hs : 0 < s := lt_min hs0 hR
  have hsR : s ≤ R := min_le_right _ _
  have hss0 : s ≤ s0 := min_le_left _ _
  have hdecay' (y : LoopPlane) (hy : y ∈ closedBall x (s / 2)) (r : ℝ)
      (hr : 0 < r) (hrs : r ≤ s / 2) :
      (∫ z in closedBall y r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        Λ * r ^ (2 * β) :=
    hdecay y (closedBall_subset_closedBall (by linarith) hy) r hr (by linarith)
  have hX1 := weak_harmonic_contDiffAt DE x hR X hXc _ hε hcap
    (fun k φ hc hs => (hEq k φ hc hs).2) hs hsR hβ hΛ.le hdecay'
  have heqX : X.value = extChartAt (𝓡 3) (q x) ∘ q := funext hX
  have hq1 : ContMDiffAt (𝓡 2) (𝓡 3) 1 q x := by
    apply contMDiffAt_iff_target.mpr
    refine ⟨hqc.continuousAt (hU.mem_nhds hx), ?_⟩
    apply contMDiffAt_iff_contDiffAt.mpr
    rwa [heqX] at hX1
  exact hq1.contMDiffWithinAt

theorem exists_C1_representative {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {U : Set LoopPlane} (hU : IsOpen U) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) :
    ∃ q : LoopPlane → M, ContMDiffOn (𝓡 2) (𝓡 3) 1 q U ∧
      q =ᵐ[volume.restrict U] F.value := by
  obtain ⟨q, hqc, hq, _hholder⟩ := F.exists_holder_representative g he hinj hemb compact hU hmin
  exact ⟨q, minimum_representative_contMDiffOn g e he hinj hemb compact hU F hmin q hqc hq, hq⟩

end PoincareConjecture.M65Euler
