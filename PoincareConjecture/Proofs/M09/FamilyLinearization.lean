import PoincareConjecture.Proofs.M09.SecondOrderLinearization
import PoincareConjecture.Proofs.M09.FamilySquareRegularization
import PoincareConjecture.Proofs.M09.InitialVectorVariation
import PoincareConjecture.Proofs.M09.SquareChartAtFlow

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_variation_phase_hasDerivAt
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (x0 : M) (s : ℝ) (hs : s ∈ sqrtParameterInterval 0 b)
    (hx : A.squareFamily Z s ∈ (chartAt E x0).source) :
    let f : ℝ × ℝ → E := fun z ↦ (chartAt E x0) (A.squareFamily (Z + z.2 • W) z.1)
    let Y : ℝ → E := fun r ↦ deriv (fun u ↦ f (r, u)) 0
    let B := regularizedCoordinatePhase (squareChartMetric F T x0) (squareChartScalar F T x0)
    HasDerivAt (fun r ↦ (Y r, deriv Y r))
      (fderiv ℝ B (s, timeDerivativePhase f (s, 0)) (0, (Y s, deriv Y s))) s := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  let Ω := V.squareDomain ∩ H ⁻¹' (chartAt E x0).source
  let f : ℝ × ℝ → E := fun z ↦ (chartAt E x0) (H z)
  let B := regularizedCoordinatePhase (squareChartMetric F T x0) (squareChartScalar F T x0)
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hΩ : IsOpen Ω := hH.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt E x0).open_source
  have hf : ContDiffOn ℝ ∞ f Ω :=
    (contMDiffOn_chart.comp (hH.mono Set.inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  have hsΩ : (s, (0 : ℝ)) ∈ Ω := by
    refine ⟨V.square_contains ⟨hs, neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩, ?_⟩
    change A.squareFamily (Z + (0 : ℝ) • W) s ∈ (chartAt E x0).source
    simpa only [zero_smul, add_zero] using hx
  let U := Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt E x0).target
  let S : Set (ℝ × (E × E)) := {z | (z.1, z.2.1) ∈ U}
  have hU : IsOpen U := isOpen_Ioo.prod (chartAt E x0).open_target
  have hS : IsOpen S :=
    hU.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hB : ContDiffOn ℝ ∞ B S := regularizedCoordinatePhase_smooth _ _ U hU
    (squareChartMetric_smooth F T τmax hτmax hwindow x0)
    (squareChartScalar_smooth F hM04 T τmax hτmax hwindow x0)
    (fun z hz v hv ↦ squareChartMetric_pos F T x0 z hz.2 v hv)
  have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hsS : (s, timeDerivativePhase f (s, 0)) ∈ S :=
    ⟨htime, (chartAt E x0).map_source hsΩ.2⟩
  have hode : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun r ↦ timeDerivativePhase f (r, u))
      (B (s, timeDerivativePhase f (s, u))) s := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hΩ.mem_nhds hsΩ)] with u hu
    exact lExponentialFamily_chartPhase_hasDerivAt hM04 hτmax hwindow A
      (Z + u • W) b hb hmax x0 s hs hu.2
  exact hasDerivAt_variation_phase_of_ode f B Ω hΩ hf s hsΩ
    ((hB.contDiffAt (hS.mem_nhds hsS)).differentiableAt (by simp)) hode

end PoincareConjecture.Proofs.M09
