import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitPullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Poincare.Analysis.Calculus

theorem RiemannianMetric.pullbackCoefficients_bilinearComp_of_eventuallyEq
    {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [IsManifold (𝓡 n) ∞ Y]
    (g : RiemannianMetric n Y)
    {p q : EuclideanSpace ℝ (Fin n) → Y}
    {a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hq : MDifferentiableAt (𝓡 n) (𝓡 n) q (a x))
    (ha : DifferentiableAt ℝ a x) (heq : q ∘ a =ᶠ[𝓝 x] p) :
    (g.pullbackCoefficients q (a x)).bilinearComp (fderiv ℝ a x) (fderiv ℝ a x) =
      g.pullbackCoefficients p x := by
  ext v w
  exact g.pullbackCoefficients_comp_of_eventuallyEq hq ha heq v w

variable {M X : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]

theorem CompactSingularMetricLimit.coordinatePullback_tendstoUniformlyOn
    {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {R : SingularTimeReference G T M} {gT : RiemannianMetric 3 X} {i : X → M}
    (h : CompactSingularMetricLimit R gT i) (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin 3) → X} (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V)
    (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k ((R.flow.metric t).pullbackCoefficients (i ∘ f)))
      (iteratedFDeriv ℝ k (gT.pullbackCoefficients f)) (𝓝[<] T) K := by
  have hlocal : TendstoLocallyUniformlyOn
      (fun t => iteratedFDeriv ℝ k ((R.flow.metric t).pullbackCoefficients (i ∘ f)))
      (iteratedFDeriv ℝ k (gT.pullbackCoefficients f)) (𝓝[<] T) V := by
    apply hV.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro x hx
    let c := extChartAt (𝓡 3) (f x)
    let W : Set (EuclideanSpace ℝ (Fin 3)) := V ∩ f ⁻¹' c.source
    have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hV
      (isOpen_extChartAt_source (f x))
    have hxW : x ∈ W := ⟨hx, mem_extChartAt_source (f x)⟩
    let a : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := c ∘ f
    have hfa (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ W) :
        ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z :=
      (hf z hz.1).contMDiffAt (hV.mem_nhds hz.1)
    have ha (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ W) :
        ContDiffAt ℝ ∞ a z := by
      apply contMDiffAt_iff_contDiffAt.mp
      exact ((contMDiffOn_extChartAt (n := ∞)).contMDiffAt
        (by simpa only [extChartAt_source] using
          (isOpen_extChartAt_source (f x)).mem_nhds hz.2)).comp z (hfa z hz)
    have haW : ContDiffOn ℝ ∞ a W := fun z hz => (ha z hz).contDiffWithinAt
    have hmap : MapsTo a W c.target := fun _ hz => c.map_source hz.2
    have hcinv (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ c.target) :
        ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
      (contMDiffOn_extChartAt_symm (n := ∞) (f x)).contMDiffAt
        ((isOpen_extChartAt_target (f x)).mem_nhds hz)
    have hnear (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ W) :
        c.symm ∘ a =ᶠ[𝓝 z] f := by
      filter_upwards [hW.mem_nhds hz] with y hy
      exact c.left_inv hy.2
    have hnear_source (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ W) :
        (i ∘ c.symm) ∘ a =ᶠ[𝓝 z] i ∘ f :=
      (hnear z hz).fun_comp i
    have hsource (t : ℝ) : EqOn
        (fun z => ((R.flow.metric t).pullbackCoefficients (i ∘ c.symm) (a z)).bilinearComp
          (fderiv ℝ a z) (fderiv ℝ a z))
        ((R.flow.metric t).pullbackCoefficients (i ∘ f)) W := by
      intro z hz
      exact (R.flow.metric t).pullbackCoefficients_bilinearComp_of_eventuallyEq
        (((hi _).comp (a z) (hcinv _ (hmap hz))).mdifferentiableAt (by simp))
        ((ha z hz).differentiableAt (by simp)) (hnear_source z hz)
    have htarget : EqOn
        (fun z => (gT.pullbackCoefficients c.symm (a z)).bilinearComp
          (fderiv ℝ a z) (fderiv ℝ a z)) (gT.pullbackCoefficients f) W := by
      intro z hz
      exact gT.pullbackCoefficients_bilinearComp_of_eventuallyEq
        ((hcinv _ (hmap hz)).mdifferentiableAt (by simp))
        ((ha z hz).differentiableAt (by simp)) (hnear z hz)
    have hcompact (C : Set (EuclideanSpace ℝ (Fin 3))) (hC : IsCompact C) (hCW : C ⊆ W) :
        TendstoUniformlyOn
          (fun t => iteratedFDeriv ℝ k ((R.flow.metric t).pullbackCoefficients (i ∘ f)))
          (iteratedFDeriv ℝ k (gT.pullbackCoefficients f)) (𝓝[<] T) C := by
      have hc := smooth_convergence_pullback_bilinear_filter
        (isOpen_extChartAt_target (f x)) hW
        (gT.contDiffOn_chartCoefficients (f x)) haW hmap
        (fun t z hz => ((R.flow.metric t).contDiffAt_pullbackCoefficients
          ((hi _).comp z (hcinv z hz))).contDiffWithinAt)
        (fun m D hD hDt => h.pullbackCoefficients_tendstoUniformlyOn hi (f x) m D hD hDt)
        k C hC hCW
      apply (hc.congr (Eventually.of_forall fun t z hz => ?_)).congr_right
      · intro z hz
        exact ((Filter.eventuallyEq_of_mem (hW.mem_nhds (hCW hz))
          htarget).iteratedFDeriv ℝ k).self_of_nhds
      · exact ((Filter.eventuallyEq_of_mem (hW.mem_nhds (hCW hz))
          (hsource t)).iteratedFDeriv ℝ k).self_of_nhds
    have hWlocal := (tendstoLocallyUniformlyOn_iff_forall_isCompact hW).mpr
      (fun C hCW hC => hcompact C hC hCW)
    exact hW.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hWlocal x hxW
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlocal.mono hKV)

end PoincareConjecture
