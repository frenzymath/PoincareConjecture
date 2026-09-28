import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitLocal




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Poincare.Analysis.Calculus

theorem RiemannianMetric.pullbackCoefficients_congr_of_eventuallyEq
    {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [IsManifold (𝓡 n) ∞ Y]
    (g : RiemannianMetric n Y) {p q : EuclideanSpace ℝ (Fin n) → Y}
    {x : EuclideanSpace ℝ (Fin n)} (h : p =ᶠ[𝓝 x] q) :
    g.pullbackCoefficients p x = g.pullbackCoefficients q x := by
  ext v w
  change g.inner (p x) (mfderiv (𝓡 n) (𝓡 n) p x v) (mfderiv (𝓡 n) (𝓡 n) p x w) =
    g.inner (q x) (mfderiv (𝓡 n) (𝓡 n) q x v) (mfderiv (𝓡 n) (𝓡 n) q x w)
  rw [h.mfderiv_eq, h.self_of_nhds]

theorem RiemannianMetric.pullbackCoefficients_eventuallyEq
    {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [IsManifold (𝓡 n) ∞ Y]
    (g : RiemannianMetric n Y) {p q : EuclideanSpace ℝ (Fin n) → Y}
    {x : EuclideanSpace ℝ (Fin n)} (h : p =ᶠ[𝓝 x] q) :
    g.pullbackCoefficients p =ᶠ[𝓝 x] g.pullbackCoefficients q := by
  filter_upwards [h.eventually_nhds] with y hy
  exact g.pullbackCoefficients_congr_of_eventuallyEq hy

namespace SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  (Q : SingularLimitConclusion H) [Nonempty (Q.extension.extended.slice T).carrier]

theorem sourceInverseCoordinate_tendstoUniformlyOn
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    {p : EuclideanSpace ℝ (Fin 3) → M}
    (hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p V)
    (hmap : MapsTo p V H.reference.regularLimitSet)
    (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k ((H.reference.flow.metric t).pullbackCoefficients p))
      (iteratedFDeriv ℝ k
        (Q.terminal_metric.pullbackCoefficients (Q.sourceInverse ∘ p))) (𝓝[<] T) K := by
  have hf := Q.sourceInverse_contMDiffOn.comp hp hmap
  have hc := Q.metric_limit_on_compacts.coordinatePullback_tendstoUniformlyOn
    Q.terminal_source_smooth hV hf k K hK hKV
  apply hc.congr
  refine Eventually.of_forall fun t x hx => ?_
  have heq : Q.terminal_source ∘ (Q.sourceInverse ∘ p) =ᶠ[𝓝 x] p := by
    filter_upwards [hV.mem_nhds (hKV hx)] with y hy
    exact Q.source_sourceInverse (hmap hy)
  exact (((H.reference.flow.metric t).pullbackCoefficients_eventuallyEq heq).iteratedFDeriv
    ℝ k).self_of_nhds

theorem sourceInverseCoordinate_scalar_tendstoUniformlyOn
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    {p : EuclideanSpace ℝ (Fin 3) → M}
    (hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p V)
    (hmap : MapsTo p V H.reference.regularLimitSet)
    (k : ℕ) (a b : Fin 3) (K : Set (EuclideanSpace ℝ (Fin 3)))
    (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k (surgeryMetricCoefficient (H.reference.flow.metric t) p a b))
      (iteratedFDeriv ℝ k
        (surgeryMetricCoefficient Q.terminal_metric (Q.sourceInverse ∘ p) a b)) (𝓝[<] T) K := by
  let E := EuclideanSpace ℝ (Fin 3)
  let B := E →L[ℝ] E →L[ℝ] ℝ
  let ev := linearJetEvaluation (E := E) (B := B) (F := ℝ) k (bilinearBasisEvaluation a b)
  have hc := ev.uniformContinuous.comp_tendstoUniformlyOn
    (Q.sourceInverseCoordinate_tendstoUniformlyOn hV hp hmap k K hK hKV)
  have hf := Q.sourceInverse_contMDiffOn.comp hp hmap
  apply (hc.congr (Eventually.of_forall fun t x hx => ?_)).congr_right
  · intro x hx
    exact ((bilinearBasisEvaluation a b).iteratedFDeriv_comp_left
      (Q.terminal_metric.contDiffAt_pullbackCoefficients
        ((hf x (hKV hx)).contMDiffAt (hV.mem_nhds (hKV hx))))
      (by exact_mod_cast le_top)).symm
  · exact ((bilinearBasisEvaluation a b).iteratedFDeriv_comp_left
      ((H.reference.flow.metric t).contDiffAt_pullbackCoefficients
        ((hp x (hKV hx)).contMDiffAt (hV.mem_nhds (hKV hx))))
      (by exact_mod_cast le_top)).symm

theorem sourceInverse_surgeryMetricLimitOn :
    SurgeryMetricLimitOn Q.referenceCarrier (Q.extension.extended.slice T)
      H.reference.flow.metric Q.terminal_metric Q.sourceInverse H.reference.regularLimitSet T := by
  intro q _ K hK hKt hKU k a b ε hε
  let c := extChartAt (𝓡 3) q
  let V := c.target ∩ c.symm ⁻¹' H.reference.regularLimitSet
  have hV : IsOpen V := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target q) Q.regular_open
  have hKV : K ⊆ V := fun x hx => ⟨hKt hx, hKU ⟨x, hx, rfl⟩⟩
  have hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm V :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).mono inter_subset_left
  have hconv := Q.sourceInverseCoordinate_scalar_tendstoUniformlyOn hV hp
    (fun _ hx => hx.2) k a b K hK hKV
  have he := Metric.tendstoUniformlyOn_iff.mp hconv ε hε
  obtain ⟨t₀, ht₀, hbound⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  refine ⟨T - t₀, sub_pos.mpr ht₀, fun t ht htT x hx => ?_⟩
  have h := hbound ⟨by linarith, htT⟩ x hx
  have hcoeff : surgeryMetricCoefficient (H.reference.flow.metric t) c.symm a b =
      singularMetricCoefficient (H.reference.flow.metric t) q a b := by
    rfl
  rw [hcoeff] at h
  simpa only [dist_eq_norm, norm_sub_rev, c, Function.comp_def] using h

end SingularLimitConclusion
end PoincareConjecture
