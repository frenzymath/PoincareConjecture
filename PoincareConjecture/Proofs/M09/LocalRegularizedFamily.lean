import PoincareConjecture.Proofs.M09.SquareChartFlow
import PoincareConjecture.Proofs.M09.ChartCurveEquation
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

local notation "E" => EuclideanSpace ℝ (Fin n)

structure LocalRegularizedInitialFamily {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (Z0 : TangentSpace (𝓡 n) p) where
  radius : ℝ
  radius_pos : 0 < radius
  neighborhood : Set (TangentSpace (𝓡 n) p)
  neighborhood_open : IsOpen neighborhood
  center_mem : Z0 ∈ neighborhood
  curve : TangentSpace (𝓡 n) p → ℝ → M
  curve_smooth :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun z ↦ curve z.1 z.2) (neighborhood ×ˢ Set.Ioo (-radius) radius)
  curve_start : ∀ Z ∈ neighborhood, curve Z 0 = p
  initial_derivative : ∀ Z (hZ : Z ∈ neighborhood),
    (curve_start Z hZ) ▸ curveVelocity (n := n) (curve Z) 0 = (2 : ℝ) • Z
  time_mem : ∀ s ∈ Set.Ioo (-radius) radius, T - s ^ 2 ∈ J
  velocity_extension : ∀ Z ∈ neighborhood,
    ParametricAlongCurveExtensionOn (n := n) (Set.Ioo (-radius) radius) (curve Z)
      (curveVelocityWithin (n := n) (curve Z) (Set.Ioo (-radius) radius))
  equation : ∀ Z (hZ : Z ∈ neighborhood), ∀ s ∈ Set.Ioo (-radius) radius,
    regularizedLGeodesicEquation F T (curve Z) (Set.Ioo (-radius) radius)
      (velocity_extension Z hZ) s

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_localRegularizedInitialFamily {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (Z0 : TangentSpace (𝓡 n) p) :
    Nonempty (LocalRegularizedInitialFamily F T p Z0) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let e := chartAt E p
  let L : TangentSpace (𝓡 n) p →L[ℝ] E := mfderiv (𝓡 n) (𝓡 n) e p
  let q : TangentSpace (𝓡 n) p → E × E := fun Z ↦ (e p, (2 : ℝ) • L Z)
  have hq : ContDiff ℝ ∞ q := contDiff_const.prodMk (L.contDiff.const_smul (2 : ℝ))
  obtain ⟨beta, W, d, hW, hq0, _, hd, hbeta, hbeta0, hbetaODE⟩ :=
    exists_squareChart_initial_flow F hM04 T b hb hwindow p
      (e p) ((2 : ℝ) • L Z0) (e.map_source (mem_chart_source E p))
  let N : Set (TangentSpace (𝓡 n) p) := q ⁻¹' W
  let I : Set ℝ := Set.Ioo (-d) d
  let a : TangentSpace (𝓡 n) p → ℝ → E := fun Z s ↦ (beta (q Z, s)).1
  let v : TangentSpace (𝓡 n) p → ℝ → E := fun Z s ↦ (beta (q Z, s)).2
  let c : TangentSpace (𝓡 n) p → ℝ → M := fun Z s ↦ e.symm (a Z s)
  have hN : IsOpen N := hW.preimage hq.continuous
  have hZ0 : Z0 ∈ N := hq0
  have hI : IsOpen I := isOpen_Ioo
  have h0 : (0 : ℝ) ∈ I := ⟨neg_lt_zero.mpr hd, hd⟩
  have hmap : ContDiff ℝ ∞
      (fun z : TangentSpace (𝓡 n) p × ℝ ↦ (q z.1, z.2)) :=
    (hq.comp contDiff_fst).prodMk contDiff_snd
  have hbmap : ContDiffOn ℝ ∞
      (fun z : TangentSpace (𝓡 n) p × ℝ ↦ beta (q z.1, z.2)) (N ×ˢ I) :=
    hbeta.comp hmap.contDiffOn (fun z hz ↦ ⟨hz.1, hz.2⟩)
  have hy : ∀ Z ∈ N, ∀ s ∈ I, a Z s ∈ e.target :=
    fun Z hZ s hs ↦ (hbetaODE (q Z) hZ s hs).2.1
  have htime : I ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b) :=
    fun s hs ↦ (hbetaODE (q Z0) hZ0 s hs).1
  have ha : ∀ Z ∈ N, ∀ s ∈ I, HasDerivAt (a Z) (v Z s) s := by
    intro Z hZ s hs
    exact (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt s
      (hbetaODE (q Z) hZ s hs).2.2
  have hdv : ∀ Z ∈ N, ∀ s ∈ I, HasDerivAt (v Z)
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (a Z s, v Z s))).2 s := by
    intro Z hZ s hs
    exact (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt s
      (hbetaODE (q Z) hZ s hs).2.2
  have hv : ∀ Z ∈ N, ContDiffOn ℝ ∞ (v Z) I := by
    intro Z hZ
    exact contDiff_snd.contDiffOn.comp
      (hbeta.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun s hs ↦ ⟨hZ, hs⟩)) (fun _ _ ↦ Set.mem_univ _)
  have hc : ContMDiffOn ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun z ↦ c z.1 z.2) (N ×ˢ I) := by
    have haSmooth : ContDiffOn ℝ ∞
        (fun z : TangentSpace (𝓡 n) p × ℝ ↦ a z.1 z.2) (N ×ˢ I) :=
      contDiff_fst.contDiffOn.comp hbmap (fun _ _ ↦ Set.mem_univ _)
    have haM : ContMDiffOn ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ)))
        (𝓡 n) ∞ (fun z ↦ a z.1 z.2) (N ×ˢ I) := by
      convert! haSmooth.contMDiffOn using 1 <;>
        simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiffOn_chart_symm.comp haM
      (fun z hz ↦ hy z.1 hz.1 z.2 hz.2)
  have hstart : ∀ Z ∈ N, c Z 0 = p := by
    intro Z hZ
    change e.symm (beta (q Z, 0)).1 = p
    rw [hbeta0 (q Z) hZ]
    exact e.left_inv (mem_chart_source E p)
  have hinitial : ∀ Z (hZ : Z ∈ N),
      (hstart Z hZ) ▸ curveVelocity (n := n) (c Z) 0 = (2 : ℝ) • Z := by
    intro Z hZ
    have hvel := curveVelocityWithin_inverseChart p (a Z) I 0 (v Z 0)
      (hI.uniqueDiffOn 0 h0) (ha Z hZ 0 h0) (hy Z hZ 0 h0)
    have htotal : curveVelocityWithin (n := n) (c Z) I 0 =
        curveVelocity (n := n) (c Z) 0 := by
      unfold curveVelocityWithin curveVelocity
      rw [mfderivWithin_of_isOpen hI h0]
    rw [htotal] at hvel
    have hz : a Z 0 = e p := congrArg Prod.fst (hbeta0 (q Z) hZ)
    have hvz : v Z 0 = (2 : ℝ) • L Z := congrArg Prod.snd (hbeta0 (q Z) hZ)
    have hinv := congrArg (fun A : TangentSpace (𝓡 n) p →L[ℝ]
        TangentSpace (𝓡 n) p ↦ A Z)
      ((mdifferentiable_chart (I := 𝓡 n) p).symm_comp_deriv (mem_chart_source E p))
    have hcast (x y : M) (h : x = y) (w : TangentSpace (𝓡 n) x) :
        (h ▸ w : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from w) := by
      cases h
      rfl
    rw [hcast _ _ (hstart Z hZ) (curveVelocity (n := n) (c Z) 0)]
    change curveVelocity (n := n) (c Z) 0 = (2 : ℝ) • Z
    calc
      _ = mfderiv (𝓡 n) (𝓡 n) e.symm (a Z 0) (v Z 0) := hvel
      _ = mfderiv (𝓡 n) (𝓡 n) e.symm (e p) ((2 : ℝ) • L Z) := by rw [hz, hvz]
      _ = (2 : ℝ) • Z := by rw [map_smul]; exact congrArg ((2 : ℝ) • ·) hinv
  let ext := fun Z (hZ : Z ∈ N) ↦
    chartCurveVelocityExtension p (a Z) (v Z) I I hI (Set.Subset.refl I)
      hI.uniqueDiffOn (hv Z hZ) (ha Z hZ) (hy Z hZ)
  refine ⟨{
    radius := d
    radius_pos := hd
    neighborhood := N
    neighborhood_open := hN
    center_mem := hZ0
    curve := c
    curve_smooth := hc
    curve_start := hstart
    initial_derivative := hinitial
    time_mem := fun s hs ↦ hwindow (squareTime_mem_window T hb (htime hs))
    velocity_extension := ext
    equation := ?_
  }⟩
  intro Z hZ s hs
  exact chartCurve_regularized_equation F hM04 T b hb hwindow p (a Z) (v Z)
    I I hI (Set.Subset.refl I) hI.uniqueDiffOn (hv Z hZ) (ha Z hZ) (hy Z hZ)
    htime (hdv Z hZ) s hs

end PoincareConjecture.Proofs.M09
