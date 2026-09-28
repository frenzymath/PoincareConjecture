import PoincareConjecture.Proofs.M09.ParameterCurvePhase
import PoincareConjecture.Proofs.M09.FamilySquareRegularization
import PoincareConjecture.Proofs.M09.InitialVectorVariation
import PoincareConjecture.Proofs.M09.LinearizedODE
import PoincareConjecture.Proofs.M09.SquareChartAtFlow








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

noncomputable def initialLinePhase (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (z : ℝ × ℝ) : TangentBundle (𝓡 n) M :=
  curvePhase (n := n) (A.squareFamily (Z + z.2 • W)) z.1

noncomputable def initialLineChartPhase (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (x : M) (z : ℝ × ℝ) : Q × Q :=
  tangentChartPhase x (initialLinePhase A Z W z)

set_option backward.isDefEq.respectTransparency false in
theorem initialLinePhase_contMDiffOn (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞ (initialLinePhase A Z W)
      (initialVectorVariation A Z W b hb hmax).squareDomain := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z ↦ V.squareFamily z.1 z.2) V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact parameterCurvePhase_contMDiffOn _ _ V.square_open hH

set_option backward.isDefEq.respectTransparency false in
theorem initialLineChartPhase_contDiffOn (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (x : M) :
    ContDiffOn ℝ ∞ (initialLineChartPhase A Z W x)
      ((initialVectorVariation A Z W b hb hmax).squareDomain ∩
        (fun z : ℝ × ℝ ↦ A.squareFamily (Z + z.2 • W) z.1) ⁻¹' (chartAt Q x).source) := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z ↦ V.squareFamily z.1 z.2) V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact tangentChartPhase_parameter_contDiffOn _ _ V.square_open hH x

theorem lExponentialFamily_tangentChartPhase_hasDerivAt
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (x : M) (s : ℝ) (hs : s ∈ sqrtParameterInterval 0 b)
    (hx : A.squareFamily Z s ∈ (chartAt Q x).source) :
    HasDerivAt (fun r ↦ tangentChartPhase x (curvePhase (n := n) (A.squareFamily Z) r))
      (regularizedCoordinatePhase (squareChartMetric F T x) (squareChartScalar F T x)
        (s, tangentChartPhase x (curvePhase (n := n) (A.squareFamily Z) s))) s := by
  let R := lExponentialFamily_squarePath A Z b hb hmax
  let U := R.domain ∩ R.curve ⁻¹' (chartAt Q x).source
  have hU : IsOpen U := R.smooth.continuousOn.isOpen_inter_preimage R.open_domain
    (chartAt Q x).open_source
  have hsU : s ∈ U := ⟨R.interval_subset hs, hx⟩
  let a : ℝ → Q := fun r ↦ (chartAt Q x) (A.squareFamily Z r)
  have heq : (fun r ↦ tangentChartPhase x (curvePhase (n := n) (A.squareFamily Z) r))
      =ᶠ[𝓝 s] (fun r ↦ (a r, deriv a r)) := by
    filter_upwards [hU.mem_nhds hsU] with r hr
    have hd := (R.smooth.contMDiffAt (R.open_domain.mem_nhds hr.1)).mdifferentiableAt (by simp)
    apply Prod.ext
    · rfl
    · exact (hasDerivAt_chart_curve x R.curve r hr.2 hd).deriv.symm
  have hode := lExponentialFamily_chartPhase_hasDerivAt hM04 hτmax hwindow A Z b hb hmax
    x s hs hx
  rw [heq.eq_of_nhds]
  exact hode.congr_of_eventuallyEq heq

set_option backward.isDefEq.respectTransparency false in
theorem initialLineChartPhase_variation_hasDerivAt
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (x : M) (s : ℝ) (hs : s ∈ sqrtParameterInterval 0 b)
    (hx : A.squareFamily Z s ∈ (chartAt Q x).source) :
    let P := initialLineChartPhase A Z W x
    let D : ℝ → Q × Q := fun r ↦ deriv (fun u ↦ P (r, u)) 0
    let B := regularizedCoordinatePhase (squareChartMetric F T x) (squareChartScalar F T x)
    HasDerivAt D (fderiv ℝ B (s, P (s, 0)) (0, D s)) s := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  let Ω := V.squareDomain ∩ H ⁻¹' (chartAt Q x).source
  let P := initialLineChartPhase A Z W x
  let B := regularizedCoordinatePhase (squareChartMetric F T x) (squareChartScalar F T x)
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hΩ : IsOpen Ω := hH.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt Q x).open_source
  have hP : ContDiffOn ℝ ∞ P Ω := initialLineChartPhase_contDiffOn A Z W b hb hmax x
  have hsΩ : (s, (0 : ℝ)) ∈ Ω := by
    refine ⟨V.square_contains ⟨hs, neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩, ?_⟩
    change A.squareFamily (Z + (0 : ℝ) • W) s ∈ (chartAt Q x).source
    simpa only [zero_smul, add_zero] using hx
  let U := Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt Q x).target
  let S : Set (ℝ × (Q × Q)) := {z | (z.1, z.2.1) ∈ U}
  have hU : IsOpen U := isOpen_Ioo.prod (chartAt Q x).open_target
  have hS : IsOpen S := hU.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hB : ContDiffOn ℝ ∞ B S := regularizedCoordinatePhase_smooth _ _ U hU
    (squareChartMetric_smooth F T τmax hτmax hwindow x)
    (squareChartScalar_smooth F hM04 T τmax hτmax hwindow x)
    (fun z hz v hv ↦ squareChartMetric_pos F T x z hz.2 v hv)
  have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hsS : (s, P (s, 0)) ∈ S := ⟨htime, (chartAt Q x).map_source hsΩ.2⟩
  have hode : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun r ↦ P (r, u)) (B (s, P (s, u))) s := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hΩ.mem_nhds hsΩ)] with u hu
    exact lExponentialFamily_tangentChartPhase_hasDerivAt hM04 hτmax hwindow A
      (Z + u • W) b hb hmax x s hs hu.2
  exact hasDerivAt_variation_of_ode P B s (hP.contDiffAt (hΩ.mem_nhds hsΩ))
    ((hB.contDiffAt (hS.mem_nhds hsS)).differentiableAt (by simp)) hode

end PoincareConjecture.Proofs.M09
