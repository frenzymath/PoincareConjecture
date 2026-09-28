import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.SpacetimeJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.FixedPullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Composition








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem tendstoUniformlyOn_parametrized_spacetime_jets
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → G.limitCarrier.carrier}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U) (r : ℕ)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKU : K ⊆ Ioo a b ×ˢ U) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.flow (G.subsequence k)).metricAt z.1).pullbackCoefficients
          (fun y => ((G.embedding k).toFun (0, f y)).2) z.2))
      (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (G.limitFlow.metricAt z.1).pullbackCoefficients f z.2)) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_Ioo.prod hU)).mp ?_ K hKU hK
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  let q := f z.2
  let c := extChartAt (𝓡 n) q
  let V := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU
    (isOpen_extChartAt_source (I := 𝓡 n) q)
  have hzV : z.2 ∈ V := ⟨hz.2, mem_extChartAt_source q⟩
  let α : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := c ∘ f
  have hα : ContDiffOn ℝ ∞ α V := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact (contMDiffOn_extChartAt (n := ∞) (x := q)).comp (hf.mono inter_subset_left)
      (fun _ hx => by simpa only [c, extChartAt_source] using hx.2)
  have hαV : MapsTo α V c.target := fun x hx => c.map_source hx.2
  have hB₀ : ContDiffOn ℝ ∞
      (fun y : ℝ × EuclideanSpace ℝ (Fin n) =>
        (G.limitFlow.metricAt y.1).pullbackCoefficients c.symm y.2) (Ioo a b ×ˢ c.target) := by
    intro y hy
    exact (G.limitFlow.flow.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Ioo
      ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy.2)) hy.1).contDiffWithinAt
  have hjet := smooth_convergence_fixed_spacetime_bilinear_pullback isOpen_Ioo hV
    (isOpen_extChartAt_target (I := 𝓡 n) q) hα hαV hB₀
    (G.locally_eventually_contDiff_spatialSpacetimeCoefficients hzero q)
    (fun m A hA hAU => G.tendstoUniformlyOn_spatialSpacetimeCoefficients_jets hzero q m hA hAU)
  obtain ⟨C, hC, hzC, hCV⟩ := exists_compact_between isCompact_singleton hV
    (singleton_subset_iff.mpr hzV)
  have hCf : ContinuousOn f C := hf.continuousOn.mono (hCV.trans inter_subset_left)
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (hC.image_of_continuousOn hCf)
  let W := Ioo a b ×ˢ interior C
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_interior
  have hzW : z ∈ W := ⟨hz.1, hzC (mem_singleton z.2)⟩
  have hWV : W ⊆ Ioo a b ×ˢ V := fun y hy => ⟨hy.1, hCV (interior_subset hy.2)⟩
  obtain ⟨A, ⟨hAn, hA⟩, hAW⟩ := (compact_basis_nhds z).mem_iff.mp (hW.mem_nhds hzW)
  refine ⟨A, nhdsWithin_le_nhds hAn, ((hjet r A hA (hAW.trans hWV)).congr ?_).congr_right ?_⟩
  · filter_upwards [eventually_ge_atTop s] with k hk y hy
    have heq : EqOn
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (G.spatialSpacetimeCoefficients q k (p.1, α p.2)).bilinearComp
            (fderiv ℝ α p.2) (fderiv ℝ α p.2))
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.flow (G.subsequence k)).metricAt p.1).pullbackCoefficients
            (fun x => ((G.embedding k).toFun (0, f x)).2) p.2) W := by
      intro p hp
      have hpV := (hWV hp).2
      have hfs : f p.2 ∈ G.exhaustion k :=
        G.exhaustion_monotone hk (hs (mem_image_of_mem f (interior_subset hp.2)))
      let ψ := fun x => ((G.embedding k).toFun (0, c.symm x)).2
      have hψ : MDifferentiableAt (𝓡 n) (𝓡 n) ψ (α p.2) := by
        have hcs : c.symm (α p.2) = f p.2 := c.left_inv hpV.2
        have hh := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hfs
        rw [← hcs] at hh
        exact (hh.comp _ ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
          ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (hαV hpV)))).mdifferentiableAt
            (by simp)
      have hcompose : ψ ∘ α =ᶠ[𝓝 p.2]
          (fun x => ((G.embedding k).toFun (0, f x)).2) := by
        filter_upwards [hV.mem_nhds hpV] with x hx
        dsimp only [ψ, α, Function.comp_apply]
        rw [c.left_inv hx.2]
      ext v w
      exact ((S.flow (G.subsequence k)).metricAt p.1).pullbackCoefficients_comp_of_eventuallyEq
        hψ ((hα.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)) hcompose v w
    exact (eqOn_iteratedFDeriv_of_isOpen hW heq r) (hAW hy)
  · intro y hy
    have heq : EqOn
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((G.limitFlow.metricAt p.1).pullbackCoefficients c.symm (α p.2)).bilinearComp
            (fderiv ℝ α p.2) (fderiv ℝ α p.2))
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (G.limitFlow.metricAt p.1).pullbackCoefficients f p.2) W := by
      intro p hp
      have hpV := (hWV hp).2
      have hcompose : c.symm ∘ α =ᶠ[𝓝 p.2] f := by
        filter_upwards [hV.mem_nhds hpV] with x hx
        exact c.left_inv hx.2
      ext v w
      exact (G.limitFlow.metricAt p.1).pullbackCoefficients_comp_of_eventuallyEq
        (((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
          ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (hαV hpV))).mdifferentiableAt
            (by simp))
        ((hα.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)) hcompose v w
    exact (eqOn_iteratedFDeriv_of_isOpen hW heq r) (hAW hy)

end PoincareConjecture.PointedGeometricConvergence
