import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.ScalarNormalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Parametrization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]

theorem eventually_scalarNormalized_parametrized_jets_at_of_chart_bound
    (F : RicciFlow 3 M (Iic 0))
    (q : M) {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (extChartAt (𝓡 3) q).source)
    {ι : Type*} (f : ι → E → M)
    (hf : ∀ i, ∃ U, IsOpen U ∧ (0 : E) ∈ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f i) U)
    (hmap : ∀ i, f i 0 ∈ K)
    (m : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hfj : ∀ i j, 1 ≤ j → j ≤ m + 1 →
      ‖iteratedFDeriv ℝ j ((extChartAt (𝓡 3) q) ∘ f i) 0‖ ≤ C)
    {κ : Type*} {l : Filter κ}
    {r : ℝ} (hr : 0 < r) {s : κ → ℝ} (hs : Tendsto s l (𝓝 r))
    (tau : κ → ℝ) (htau : ∀ k, tau k ∈ Icc (-1 : ℝ) 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in l, ∀ i j, j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y =>
        s k • (F.metric (tau k / s k)).parametrizedCoefficients (f i) y -
        r • (F.metric (tau k / r)).parametrizedCoefficients (f i) y) 0‖ ≤ eta := by
  let c := extChartAt (𝓡 3) q
  let alpha := fun i => c ∘ f i
  let L := c '' K
  have hL : IsCompact L := hK.image_of_continuousOn
    ((continuousOn_extChartAt q).mono hKchart)
  have hLc : L ⊆ c.target := image_subset_iff.mpr fun x hx => c.map_source (hKchart hx)
  have halpha (i : ι) : ContDiffAt ℝ ∞ (alpha i) 0 := by
    obtain ⟨U, hU, h0, hfi⟩ := hf i
    exact contMDiffAt_iff_contDiffAt.mp
      (((contMDiffOn_extChartAt (n := ∞) (x := q)).contMDiffAt
        (by simpa only [extChartAt_source] using
          (isOpen_extChartAt_source (I := 𝓡 3) q).mem_nhds (hKchart (hmap i)))).comp 0
          (hfi.contMDiffAt (hU.mem_nhds h0)))
  have hcoef (t : ℝ) (y : E) (hy : y ∈ c.target) :
      ContDiffAt ℝ ∞ ((F.metric t).parametrizedCoefficients c.symm) y :=
    (F.metric t).contDiffAt_parametrizedCoefficients
      ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target q).mem_nhds hy))
  let B := fun k y => s k • (F.metric (tau k / s k)).parametrizedCoefficients c.symm y -
    r • (F.metric (tau k / r)).parametrizedCoefficients c.symm y
  have hBs : ∀ᶠ k in l, ∀ y ∈ L, ContDiffAt ℝ ∞ (B k) y := by
    filter_upwards [] with k y hy
    exact ((hcoef _ y (hLc hy)).const_smul (s k)).sub
      ((hcoef _ y (hLc hy)).const_smul r)
  have hBj : ∀ delta : ℝ, 0 < delta → ∀ᶠ k in l, ∀ y ∈ L, ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j (B k) y‖ ≤ delta := by
    intro delta hdelta
    have he (j : ℕ) : ∀ᶠ k in l, ∀ y ∈ L,
        ‖iteratedFDeriv ℝ j (B k) y‖ ≤ delta := by
      have hc := F.tendstoUniformlyOn_scalarNormalized_spatialJets
        (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm (n := ∞) q)
        hL hLc hr hs j
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc delta hdelta] with k hk y hy
      have h := (hk (tau k, y) ⟨htau k, hy⟩).le
      rw [dist_comm, dist_eq_norm] at h
      rw [show iteratedFDeriv ℝ j (B k) y =
          iteratedFDeriv ℝ j (fun z => s k •
            (F.metric (tau k / s k)).parametrizedCoefficients c.symm z) y -
          iteratedFDeriv ℝ j (fun z => r •
            (F.metric (tau k / r)).parametrizedCoefficients c.symm z) y from
        iteratedFDeriv_sub_apply
          (((hcoef _ y (hLc hy)).const_smul (s k)).of_le
            (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤)))
          (((hcoef _ y (hLc hy)).const_smul r).of_le
            (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤)))]
      exact h
    filter_upwards [(eventually_all_finite (finite_Iic m)).mpr
      (fun j _ => he j)] with k hk y hy j hj
    exact hk j hj y hy
  have hb := TerminalNeck.eventually_small_bilinearPullback_jets_at_filter
    (B := B) (f := alpha) (fun _ : ι => (0 : E)) halpha
    (fun i => mem_image_of_mem c (hmap i)) hBs m hC hfj hBj heta
  filter_upwards [hb] with k hk i j hj
  obtain ⟨U, hU, h0, hfi⟩ := hf i
  let V := U ∩ f i ⁻¹' c.source
  have hV : IsOpen V := hfi.continuousOn.isOpen_inter_preimage hU
    (isOpen_extChartAt_source (I := 𝓡 3) q)
  have h0V : (0 : E) ∈ V := ⟨h0, hKchart (hmap i)⟩
  have halphaV : ContDiffOn ℝ ∞ (alpha i) V := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact (contMDiffOn_extChartAt (n := ∞) (x := q)).comp
      (hfi.mono inter_subset_left)
      (fun y hy => by simpa only [c, extChartAt_source] using hy.2)
  have heq : (fun y => (B k (alpha i y)).bilinearComp
      (fderiv ℝ (alpha i) y) (fderiv ℝ (alpha i) y)) =ᶠ[𝓝 (0 : E)]
      (fun y => s k • (F.metric (tau k / s k)).parametrizedCoefficients (f i) y -
        r • (F.metric (tau k / r)).parametrizedCoefficients (f i) y) := by
    filter_upwards [hV.mem_nhds h0V] with y hy
    have hcs := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds (c.map_source hy.2))
    have hcomp : c.symm ∘ alpha i =ᶠ[𝓝 y] f i := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact c.left_inv hz.2
    have hdiff := (halphaV.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
    have hsource := (F.metric (tau k / s k)).parametrizedCoefficients_comp_of_eventuallyEq
      (hcs.mdifferentiableAt (by simp)) hdiff hcomp
    have hlimit := (F.metric (tau k / r)).parametrizedCoefficients_comp_of_eventuallyEq
      (hcs.mdifferentiableAt (by simp)) hdiff hcomp
    ext v w
    exact congrArg₂ (fun a b : ℝ => s k * a - r * b)
      (congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) hsource)
      (congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) hlimit)
  rw [← (heq.iteratedFDeriv ℝ j).self_of_nhds]
  exact hk i j hj

end PoincareConjecture.RicciFlow
