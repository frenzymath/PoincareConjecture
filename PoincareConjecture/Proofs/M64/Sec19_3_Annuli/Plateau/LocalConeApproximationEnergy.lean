import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeCorrectedCurves
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeDiskEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeContinuous

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

open Proofs.M58

theorem m64_integral_norm_sq_le_twice_error
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {mu : Measure X} {f v : X → E} (hf : MemLp f 2 mu) (hv : MemLp v 2 mu) :
    (∫ x, ‖f x‖ ^ 2 ∂mu) ≤
      2 * ((∫ x, ‖f x - v x‖ ^ 2 ∂mu) + ∫ x, ‖v x‖ ^ 2 ∂mu) := by
  have hfi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hvi := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hdi : Integrable (fun x => ‖f x - v x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm
    (hf.sub hv).aestronglyMeasurable).mp (hf.sub hv)
  rw [← integral_add hdi hvi, ← integral_const_mul]
  apply integral_mono hfi ((hdi.add hvi).const_mul 2)
  intro x
  have hn : ‖f x‖ ≤ ‖f x - v x‖ + ‖v x‖ := norm_le_norm_sub_add _ _
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  simp only [Pi.add_apply] at *
  nlinarith [sq_nonneg (‖f x - v x‖ - ‖v x‖)]

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

theorem m64_corrected_circle_energy_le
    (g : RiemannianMetric n M) (f : ℝ → M) (w v : ℝ → E)
    (hf : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 f) (hw : ContDiff ℝ 1 w)
    (hv : MemLp v 2 circleMu) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, g.tangentNorm (f x) (curveVelocity f x) ≤ B * ‖deriv w x‖) :
    (∫ x in Icc (0 : ℝ) curvePeriod,
      (g.tangentNorm (f x) (curveVelocity f x)) ^ 2) ≤
        2 * B ^ 2 * ((∫ x in Icc (0 : ℝ) curvePeriod, ‖deriv w x - v x‖ ^ 2) +
          ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) := by
  have hc := M04.continuous_pathSpeed g hf
  have hdc : Continuous (deriv w) := hw.continuous_deriv (by simp)
  have hd : MemLp (deriv w) 2 circleMu := by
    apply (memLp_two_iff_integrable_sq_norm hdc.aestronglyMeasurable).mpr
    exact (hdc.norm.pow 2).integrableOn_Icc
  calc
    _ ≤ B ^ 2 * ∫ x in Icc (0 : ℝ) curvePeriod, ‖deriv w x‖ ^ 2 := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on ((hc.pow 2).integrableOn_Icc)
        ((hdc.norm.pow 2).integrableOn_Icc.const_mul _) measurableSet_Icc
      intro x _
      change (g.tangentNorm (f x) (curveVelocity f x)) ^ 2 ≤ B ^ 2 * ‖deriv w x‖ ^ 2
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr
        (hb x)
      simpa +instances only [mul_pow] using! hs
    _ ≤ B ^ 2 * (2 * ((∫ x in Icc (0 : ℝ) curvePeriod, ‖deriv w x - v x‖ ^ 2) +
        ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (m64_integral_norm_sq_le_twice_error hd hv) (sq_nonneg _)
    _ = _ := by ring

variable [T2Space M]

theorem m64ChartReadable_local_cone_approximation_uniform
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M))
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (C : ℝ), IsOpen U ∧ p ∈ U ∧ 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        (∀ x, gamma x ∈ U) → ∀ (w : ℕ → ℝ → E),
          (∀ j, ContDiff ℝ 1 (w j)) → (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∀ v : ℝ → E, MemLp v 2 circleMu →
            ∃ (k : ℕ) (F : LoopPlane → M) (Fj : ℕ → LoopPlane → M),
              Continuous F ∧ (∀ x, F (angularPoint x) = gamma x) ∧
              (∀ z : LoopPlane, ‖z‖ ≤ 1 / 2 → F z = gamma 0) ∧
              (∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (Fj j)) ∧
              (∀ z, Tendsto (fun j => Fj j z) atTop (𝓝 (F z))) ∧
              TendstoUniformlyOn (fun j x => e (Fj j (angularPoint x))) (e ∘ gamma) atTop
                (Icc (0 : ℝ) curvePeriod) ∧
              ∀ j, (∫ z in loopDiskSet, m60EnergyDensity g (Fj j) z) ≤
                C * ((∫ x in Icc (0 : ℝ) curvePeriod, ‖deriv (w (j + k)) x - v x‖ ^ 2) +
                  ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨r, hr, B, _, H, hH, hgeom, _⟩ := m64_exists_local_cone_interpolator g hcompact
  obtain ⟨P, _, hprofile⟩ := exists_diskTimeProfile_derivative_bound
  let A : ℝ := P ^ 2 / 2 * curvePeriod ^ 2 + 2 * B ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let O : Set M := {q | g.edist p q < ENNReal.ofReal (r / 8)}
  have hO : IsOpen O := isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hpO : p ∈ O := by
    change edist p p < ENNReal.ofReal (r / 8)
    rw [edist_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨U, D, hU, hpU, hD, happ⟩ :=
    m64ChartReadable_local_circle_approximation_uniform g e he hread p O hO hpO
  refine ⟨U, 2 * A * D ^ 2, hU, hpU, by positivity, ?_⟩
  intro gamma hgamma hgammaP hgammaU w hw hwP hlim v hv
  obtain ⟨k, f, hfc, hfP, hfpoint, hfO, hfuniform, hspeed⟩ :=
    happ gamma hgammaP hgammaU w hw hwP hlim
  have hfshort (j : ℕ) (x : ℝ) :
      g.edist (f j 0) (f j x) ≤ ENNReal.ofReal (r / 2) := by
    calc
      _ ≤ g.edist (f j 0) p + g.edist p (f j x) := Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal (r / 8) + ENNReal.ofReal (r / 8) :=
        add_le_add (by
          rw [show g.edist (f j 0) p = g.edist p (f j 0) from Manifold.riemannianEDist_comm]
          exact (hfO j 0).le) (hfO j x).le
      _ ≤ ENNReal.ofReal (r / 2) := by
        rw [← ENNReal.ofReal_add (by linarith : 0 ≤ r / 8) (by linarith : 0 ≤ r / 8)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  have hgshort (x : ℝ) : g.edist (gamma 0) (gamma x) ≤ ENNReal.ofReal (r / 2) :=
    le_of_tendsto ((hfpoint 0).edist (hfpoint x)) (Eventually.of_forall fun j => hfshort j x)
  have hV : IsOpen {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} :=
    isOpen_lt continuous_edist continuous_const
  have hHat (beta : ℝ → M)
      (hb : ∀ x, g.edist (beta 0) (beta x) ≤ ENNReal.ofReal (r / 2))
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 H
        (s, beta 0, beta x) := by
    apply (hH.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ?_)).of_le (by simp)
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      (hb x).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))⟩
  have h0 (beta : ℝ → M)
      (hb : ∀ x, g.edist (beta 0) (beta x) ≤ ENNReal.ofReal (r / 2)) (x : ℝ) :
      H (0, beta 0, beta x) = beta 0 := (hgeom _ _ (hb x)).1
  let F := m64LocalConeDiskMap H (gamma 0) gamma
  let Fj := fun j => m64LocalConeDiskMap H (f j 0) (f j)
  have hFj (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) 1 (Fj j) :=
    m64LocalConeDiskMap_contMDiff H (f j 0) (f j) (hfc j) (hfP j)
      (h0 _ (hfshort j)) (hHat _ (hfshort j))
  refine ⟨k, F, Fj, m64LocalConeDiskMap_continuous H (gamma 0) gamma hgamma hgammaP
    (h0 gamma hgshort) (fun s hs x => (hHat gamma hgshort s hs x).continuousAt),
    m64LocalConeDiskMap_boundary H (gamma 0) gamma hgammaP
      (fun x => (hgeom _ _ (hgshort x)).2.1),
    fun z hz => m64LocalConeDiskMap_inner H (gamma 0) gamma (h0 gamma hgshort) hz,
    hFj, ?_, ?_, ?_⟩
  · intro z
    exact m64LocalConeDiskMap_tendsto H (fun j => f j 0) f (gamma 0) gamma
      (hfpoint 0) hfpoint (fun s hs x => (hHat gamma hgshort s hs x).continuousAt) z
  · have htrace (j : ℕ) (x : ℝ) : Fj j (angularPoint x) = f j x :=
      m64LocalConeDiskMap_boundary H (f j 0) (f j) (hfP j)
        (fun x => (hgeom _ _ (hfshort j x)).2.1) x
    simpa only [htrace, Function.comp_def] using hfuniform
  · intro j
    have hc := m64LocalConeDiskMap_energy_le g H (f j) (hfc j) (hfP j)
      (h0 _ (hfshort j)) (hFj j) (hHat _ (hfshort j))
      (fun s hs x => (hgeom _ _ (hfshort j x)).2.2.1 s hs)
      (fun s hs x => (hgeom _ _ (hfshort j x)).2.2.2 s hs) hprofile
    have hd := m64_corrected_circle_energy_le g (f j) (w (j + k)) v
      (hfc j) (hw _) hv hD (hspeed j)
    exact hc.trans ((mul_le_mul_of_nonneg_left hd hA).trans_eq (by ring))

theorem m64ChartReadable_local_cone_approximation
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M))
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (C : ℝ), IsOpen U ∧ p ∈ U ∧ 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        (∀ x, gamma x ∈ U) → ∀ (w : ℕ → ℝ → E),
          (∀ j, ContDiff ℝ 1 (w j)) → (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∀ v : ℝ → E, MemLp v 2 circleMu →
            ∃ (k : ℕ) (F : LoopPlane → M) (Fj : ℕ → LoopPlane → M),
              Continuous F ∧ (∀ x, F (angularPoint x) = gamma x) ∧
              (∀ z : LoopPlane, ‖z‖ ≤ 1 / 2 → F z = gamma 0) ∧
              (∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (Fj j)) ∧
              (∀ z, Tendsto (fun j => Fj j z) atTop (𝓝 (F z))) ∧
              ∀ j, (∫ z in loopDiskSet, m60EnergyDensity g (Fj j) z) ≤
                C * ((∫ x in Icc (0 : ℝ) curvePeriod, ‖deriv (w (j + k)) x - v x‖ ^ 2) +
                  ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) := by
  obtain ⟨U, C, hU, hp, hC, happ⟩ :=
    m64ChartReadable_local_cone_approximation_uniform g hcompact e he hread p
  refine ⟨U, C, hU, hp, hC, ?_⟩
  intro gamma hc hP hmem w hw hwP hlim v hv
  obtain ⟨k, F, Fj, hF, htrace, hinner, hFj, hpoint, -, henergy⟩ :=
    happ gamma hc hP hmem w hw hwP hlim v hv
  exact ⟨k, F, Fj, hF, htrace, hinner, hFj, hpoint, henergy⟩

end PoincareConjecture
