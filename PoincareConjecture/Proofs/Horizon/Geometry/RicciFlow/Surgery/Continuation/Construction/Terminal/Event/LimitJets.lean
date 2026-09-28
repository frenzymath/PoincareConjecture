import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitSource
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback
import Mathlib.Analysis.Normed.Module.ContinuousInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace Poincare.Analysis.Calculus

theorem tendstoUniformlyOn_of_finite_linear_evaluations
    {ι α β E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : ι → E →L[ℝ] F)
    (hsep : ∀ x y, (∀ i, e i x = e i y) → x = y)
    {l : Filter α} {K : Set β} {f : α → β → E} {g : β → E}
    (h : ∀ i, TendstoUniformlyOn (fun t x => e i (f t x))
      (fun x => e i (g x)) l K) : TendstoUniformlyOn f g l K := by
  let P : E →L[ℝ] (ι → F) := ContinuousLinearMap.pi e
  have hP : Function.Injective P := fun x y hxy =>
    hsep x y (fun i => congrFun hxy i)
  obtain ⟨R, hR⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hP
  have hc : TendstoUniformlyOn (fun t x => P (f t x)) (fun x => P (g x)) l K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he : ∀ᶠ t in l, ∀ i, ∀ x ∈ K, dist (e i (g x)) (e i (f t x)) < ε :=
      eventually_all.mpr fun i => (Metric.tendstoUniformlyOn_iff.mp (h i)) ε hε
    filter_upwards [he] with t ht x hx
    exact (dist_pi_lt_iff hε).mpr fun i => ht i x hx
  have hR' (x : E) : R (P x) = x := hR x
  simpa only [Function.comp_def, hR'] using R.uniformContinuous.comp_tendstoUniformlyOn hc

theorem smooth_convergence_pullback_bilinear_filter
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {d : ℕ} {U V : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hV : IsOpen V)
    {B : α → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {B₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hB₀ : ContDiffOn ℝ ∞ B₀ U) (ha : ContDiffOn ℝ ∞ a V)
    (haU : MapsTo a V U)
    (hB : ∀ t, ContDiffOn ℝ ∞ (B t) U)
    (hjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ m (B t)) (iteratedFDeriv ℝ m B₀) l K)
    (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ m (fun y => (B t (a y)).bilinearComp
        (fderiv ℝ a y) (fderiv ℝ a y)))
      (iteratedFDeriv ℝ m (fun y => (B₀ (a y)).bilinearComp
        (fderiv ℝ a y) (fderiv ℝ a y))) l K := by
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro s hs
  exact (smooth_convergence_pullback_bilinear_on_open hU hV hB₀ ha haU
    (fun x hx => ⟨U, hU, hx, Eventually.of_forall fun k => hB (s k)⟩)
    (fun x hx => ⟨V, hV, hx, Eventually.of_forall fun _ => ha⟩)
    (fun m C hC hCU => (hjet m C hC hCU).seq_tendstoUniformlyOn s hs)
    (fun _ _ _ _ => Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
      Eventually.of_forall fun _ _ _ => by simpa using hε)).2 m K hK hKV

end Poincare.Analysis.Calculus

namespace PoincareConjecture

theorem CompactSingularMetricLimit.tendstoUniformlyOn
    {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {M X : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {R : SingularTimeReference G T M} {gT : RiemannianMetric 3 X} {i : X → M}
    (h : CompactSingularMetricLimit R gT i) (q : X) (a b : Fin 3) (k : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k
        (singularTensorCoefficient (singularMetricPullback (R.flow.metric t) i) q a b))
      (iteratedFDeriv ℝ k (singularMetricCoefficient gT q a b)) (𝓝[<] T) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨t₀, _, ht₀, hbound⟩ := h q a b k K hK hKt ε hε
  filter_upwards [Ioo_mem_nhdsLT ht₀] with t ht x hx
  simpa only [dist_eq_norm, norm_sub_rev] using hbound t ht.1 ht.2 x hx

end PoincareConjecture
