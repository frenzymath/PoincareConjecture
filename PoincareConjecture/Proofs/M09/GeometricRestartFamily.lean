import PoincareConjecture.Proofs.M09.SquareChartAtFlow
import PoincareConjecture.Proofs.M09.ChartCurveEquation
import PoincareConjecture.Proofs.M09.CurvePhase
import PoincareConjecture.Proofs.M09.VelocityRestriction
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => ℝ × (V × V)

structure LocalRegularizedRestartFamily {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (p : M) (z0 : Z) where
  neighborhood : Set Z
  neighborhood_open : IsOpen neighborhood
  center_mem : z0 ∈ neighborhood
  state_mem : ∀ z ∈ neighborhood,
    z.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ∧ z.2.1 ∈ (chartAt V p).target
  radius : ℝ
  radius_pos : 0 < radius
  curve : Z → ℝ → M
  curve_smooth : ContMDiffOn ((𝓘(ℝ, Z)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
    (fun q : Z × ℝ ↦ curve q.1 q.2)
    {q | q.1 ∈ neighborhood ∧ q.2 - q.1.1 ∈ Set.Ioo (-radius) radius}
  initial_phase : ∀ z ∈ neighborhood, curvePhase (n := n) (curve z) z.1 =
    (⟨(chartAt V p).symm z.2.1,
      (mfderiv (𝓡 n) (𝓡 n) (chartAt V p).symm z.2.1) z.2.2⟩ : TangentBundle (𝓡 n) M)
  time_mem : ∀ z ∈ neighborhood, ∀ s ∈ Set.Ioo (z.1 - radius) (z.1 + radius),
    s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)
  velocity_extension : ∀ z ∈ neighborhood,
    ParametricAlongCurveExtensionOn (n := n) (Set.Ioo (z.1 - radius) (z.1 + radius)) (curve z)
      (curveVelocityWithin (n := n) (curve z) (Set.Ioo (z.1 - radius) (z.1 + radius)))
  equation : ∀ z (hz : z ∈ neighborhood), ∀ s ∈ Set.Ioo (z.1 - radius) (z.1 + radius),
    regularizedLGeodesicEquation F T (curve z) (Set.Ioo (z.1 - radius) (z.1 + radius))
      (velocity_extension z hz) s

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_localRegularizedRestartFamily {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (p : M) (z0 : Z)
    (hz0 : z0.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ∧
      z0.2.1 ∈ (chartAt V p).target) :
    Nonempty (LocalRegularizedRestartFamily F T b p z0) := by
  let e := chartAt V p
  obtain ⟨beta, W, d, hW, hzW, hWS, hd, hbeta, hbeta0, hODE⟩ :=
    exists_squareChart_local_flow F hM04 T b hb hwindow p z0 hz0
  let Q : Set (Z × ℝ) := {q | q.1 ∈ W ∧ q.2 - q.1.1 ∈ Set.Ioo (-d) d}
  let I : Z → Set ℝ := fun z ↦ Set.Ioo (z.1 - d) (z.1 + d)
  let a : Z → ℝ → V := fun z s ↦ (beta (z, s - z.1)).1
  let v : Z → ℝ → V := fun z s ↦ (beta (z, s - z.1)).2
  let c : Z → ℝ → M := fun z s ↦ e.symm (a z s)
  have hoff (z : Z) (s : ℝ) (hs : s ∈ I z) : s - z.1 ∈ Set.Ioo (-d) d := by
    constructor <;> linarith [hs.1, hs.2]
  have h0 (z : Z) : z.1 ∈ I z := by constructor <;> linarith
  have htarget : ∀ z ∈ W, ∀ s ∈ I z, a z s ∈ e.target :=
    fun z hz s hs ↦ (hODE z hz (s - z.1) (hoff z s hs)).1.2
  have htime : ∀ z ∈ W, I z ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b) := by
    intro z hz s hs
    have h := (hODE z hz (s - z.1) (hoff z s hs)).1.1
    simpa only [add_sub_cancel] using h
  have hderiv : ∀ z ∈ W, ∀ s ∈ I z,
      HasDerivAt (fun r ↦ beta (z, r - z.1))
        (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
          (s, beta (z, s - z.1))) s := by
    intro z hz s hs
    have h := (hODE z hz (s - z.1) (hoff z s hs)).2.scomp s
      ((hasDerivAt_id s).sub_const z.1)
    convert! h using 1
    simp only [one_smul, add_sub_cancel]
  have ha : ∀ z ∈ W, ∀ s ∈ I z, HasDerivAt (a z) (v z s) s := by
    intro z hz s hs
    exact (ContinuousLinearMap.fst ℝ V V).hasFDerivAt.comp_hasDerivAt s (hderiv z hz s hs)
  have hdv : ∀ z ∈ W, ∀ s ∈ I z, HasDerivAt (v z)
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (a z s, v z s))).2 s := by
    intro z hz s hs
    exact (ContinuousLinearMap.snd ℝ V V).hasFDerivAt.comp_hasDerivAt s (hderiv z hz s hs)
  have hv : ∀ z ∈ W, ContDiffOn ℝ ∞ (v z) (I z) := by
    intro z hz
    apply contDiff_snd.contDiffOn.comp
      (hbeta.comp (contDiff_const.prodMk (contDiff_id.sub contDiff_const)).contDiffOn
        (fun s hs ↦ ⟨hz, hoff z s hs⟩))
    exact fun _ _ ↦ Set.mem_univ _
  have hmap : ContDiff ℝ ∞ (fun q : Z × ℝ ↦ (q.1, q.2 - q.1.1)) :=
    contDiff_fst.prodMk (contDiff_snd.sub (contDiff_fst.comp contDiff_fst))
  have hac : ContDiffOn ℝ ∞ (fun q : Z × ℝ ↦ a q.1 q.2) Q :=
    contDiff_fst.contDiffOn.comp (hbeta.comp hmap.contDiffOn (fun q hq ↦ hq))
      (fun _ _ ↦ Set.mem_univ _)
  have hc : ContMDiffOn ((𝓘(ℝ, Z)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun q : Z × ℝ ↦ c q.1 q.2) Q := by
    have ham : ContMDiffOn ((𝓘(ℝ, Z)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
        (fun q : Z × ℝ ↦ a q.1 q.2) Q := by
      convert! hac.contMDiffOn using 1 <;>
        simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    apply contMDiffOn_chart_symm.comp ham
    intro q hq
    exact (hODE q.1 hq.1 (q.2 - q.1.1) hq.2).1.2
  have hinitial : ∀ z ∈ W, curvePhase (n := n) (c z) z.1 =
      (⟨e.symm z.2.1, (mfderiv (𝓡 n) (𝓡 n) e.symm z.2.1) z.2.2⟩ :
        TangentBundle (𝓡 n) M) := by
    intro z hz
    have hpos : a z z.1 = z.2.1 := by
      change (beta (z, z.1 - z.1)).1 = z.2.1
      rw [sub_self, hbeta0 z hz]
    have hvel : v z z.1 = z.2.2 := by
      change (beta (z, z.1 - z.1)).2 = z.2.2
      rw [sub_self, hbeta0 z hz]
    have hcv := curveVelocityWithin_inverseChart p (a z) (I z) z.1 (v z z.1)
      (isOpen_Ioo.uniqueDiffOn z.1 (h0 z)) (ha z hz z.1 (h0 z)) (htarget z hz z.1 (h0 z))
    have hwithin : curveVelocityWithin (n := n) (c z) (I z) z.1 = curveVelocity (c z) z.1 := by
      unfold curveVelocityWithin curveVelocity
      rw [mfderivWithin_of_isOpen isOpen_Ioo (h0 z)]
    rw [hwithin, hpos, hvel] at hcv
    apply Bundle.TotalSpace.ext (congrArg e.symm hpos)
    exact heq_of_eq hcv
  let ext := fun z (hz : z ∈ W) ↦ chartCurveVelocityExtension p (a z) (v z) (I z) (I z)
    isOpen_Ioo (Set.Subset.refl _) isOpen_Ioo.uniqueDiffOn (hv z hz) (ha z hz) (htarget z hz)
  refine ⟨{
    neighborhood := W
    neighborhood_open := hW
    center_mem := hzW
    state_mem := fun z hz ↦ hWS hz
    radius := d
    radius_pos := hd
    curve := c
    curve_smooth := hc
    initial_phase := hinitial
    time_mem := htime
    velocity_extension := ext
    equation := ?_
  }⟩
  intro z hz s hs
  exact chartCurve_regularized_equation F hM04 T b hb hwindow p (a z) (v z) (I z) (I z)
    isOpen_Ioo (Set.Subset.refl _) isOpen_Ioo.uniqueDiffOn (hv z hz) (ha z hz) (htarget z hz)
    (htime z hz) (hdv z hz) s hs

end PoincareConjecture.Proofs.M09
