import PoincareConjecture.Proofs.M08.EndpointChartRegularity
import PoincareConjecture.Proofs.M08.EulerMomentum
import PoincareConjecture.Proofs.M08.SquareEulerTransport
import PoincareConjecture.Proofs.M08.MinimizerEulerLocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def restrictOpenVelocityExtension {I U : Set ℝ}
    (hI : IsOpen I) (hU : IsOpen U) (hsub : U ⊆ I) (α : ℝ → M)
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I)) :
    ParametricAlongCurveExtensionOn U α (curveVelocityWithin (n := n) α U) where
  extension := E.extension
  domain := E.domain
  open_domain := E.open_domain
  graph_mem s hs := E.graph_mem s (hsub hs)
  smooth := E.smooth
  agrees s hs := by
    rw [E.agrees s (hsub hs)]
    unfold curveVelocityWithin
    rw [mfderivWithin_of_mem_nhds (hI.mem_nhds (hsub hs)),
      mfderivWithin_of_mem_nhds (hU.mem_nhds hs)]

theorem regularizedEulerResidual_restrictOpenVelocityExtension {J I U : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (hI : IsOpen I) (hU : IsOpen U)
    (hsub : U ⊆ I) (α : ℝ → M)
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I))
    {s : ℝ} (hs : s ∈ U) (W : TangentSpace (𝓡 n) (α s)) :
    regularizedEulerResidual F T α U (restrictOpenVelocityExtension hI hU hsub α E) s W =
      regularizedEulerResidual F T α I E s W := by
  unfold regularizedEulerResidual pullbackCovariantDerivative
    restrictOpenVelocityExtension curveVelocityWithin
  rw [mfderivWithin_of_mem_nhds (hI.mem_nhds (hsub hs)),
    mfderivWithin_of_mem_nhds (hU.mem_nhds hs)]

variable [ConnectedSpace M] [T3Space M]

theorem squarePath_chart_derivative_memLp {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ a b : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hab : a < b) (hAa : Real.sqrt τ₁ ≤ a) (hbB : b ≤ Real.sqrt τ₂)
    (x : M) (hsrc : MapsTo (squareReparameterizedCurve p.curve) (Icc a b)
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContinuousOn ((extChartAt (𝓡 n) x) ∘ squareReparameterizedCurve p.curve) (Icc a b) ∧
    (∀ s ∈ Ioo a b, HasDerivAt
      ((extChartAt (𝓡 n) x) ∘ squareReparameterizedCurve p.curve)
      (deriv ((extChartAt (𝓡 n) x) ∘ squareReparameterizedCurve p.curve) s) s) ∧
    MemLp (deriv ((extChartAt (𝓡 n) x) ∘ squareReparameterizedCurve p.curve))
      2 (volume.restrict (Icc a b)) := by
  let α := squareReparameterizedCurve p.curve
  have hsub : Icc a b ⊆ Icc (Real.sqrt τ₁) (Real.sqrt τ₂) := Icc_subset_Icc hAa hbB
  have hsubo : Ioo a b ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) := Ioo_subset_Ioo hAa hbB
  have hα : ContinuousOn α (Icc a b) := (squarePath_continuousOn p).mono hsub
  have hαreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo a b) :=
    (squarePath_regular p).mono hsubo
  have hsrc' : MapsTo α (Icc a b) (extChartAt (𝓡 n) x).source := by
    simpa only [extChartAt_source] using hsrc
  refine ⟨(continuousOn_extChartAt (I := 𝓡 n) x).comp hα hsrc', ?_, ?_⟩
  · intro s hs
    have hm := ((hαreg s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt
      one_ne_zero
    have hd := (mdifferentiableAt_extChartAt (hsrc (Ioo_subset_Icc_self hs))).comp s hm
    exact hd.differentiableAt.hasDerivAt
  · obtain ⟨K, hK, hbound⟩ := hcurvature.2
    have hweighted := (referenceWeightedEnergy_bound hM04 hwindow hK hbound p hτ₂).1
    have henergy := (squarePath_referenceEnergy p (F.metric T) hweighted).1
    have hlocal : IntervalIntegrable (referenceSpeedSq (F.metric T) α) volume a b := by
      apply henergy.mono_set
      simpa only [uIcc_of_le hab.le, uIcc_of_le (Real.sqrt_le_sqrt p.ordered.le)] using hsub
    obtain ⟨c, hc, hcoercive⟩ := chart_velocity_L2_bound (F.metric T) x
      (isCompact_Icc.image_of_continuousOn hα)
      (by rintro y ⟨s, hs, rfl⟩; exact hsrc hs)
    obtain ⟨hLp, _⟩ := hcoercive hab.le α hαreg
      (fun s hs ↦ mem_image_of_mem α hs) hlocal le_rfl
    exact hLp

set_option maxHeartbeats 1000000 in
theorem squarePath_chart_phase {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ a b : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hp : IsBackwardLGeodesic F T τ₁ τ₂ p)
    (hab : a < b) (hAa : Real.sqrt τ₁ ≤ a) (hbB : b ≤ Real.sqrt τ₂)
    (x : M) (hsrc : MapsTo (squareReparameterizedCurve p.curve) (Icc a b)
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ∃ Pbar : ℝ → EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ∞ (fun s ↦
        (extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve s), Pbar s)) (Icc a b) ∧
      EqOn Pbar (fun s ↦ chartMetricOperator F T x
        (s, extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve s))
        (deriv ((extChartAt (𝓡 n) x) ∘ squareReparameterizedCurve p.curve) s)) (Ioo a b) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt (fun r ↦
        (extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve r), Pbar r))
        (closedChartEulerPhase F T x (Icc a b) s
          (extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve s), Pbar s)) (Icc a b) s := by
  let α := squareReparameterizedCurve p.curve
  let e := extChartAt (𝓡 n) x
  let u := e ∘ α
  have hsub : Icc a b ⊆ Icc (Real.sqrt τ₁) (Real.sqrt τ₂) := Icc_subset_Icc hAa hbB
  have hsubo : Ioo a b ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) := Ioo_subset_Ioo hAa hbB
  obtain ⟨hu, hud, hd⟩ := squarePath_chart_derivative_memLp hM04 hwindow hcurvature hτ₂ p
    hab hAa hbB x hsrc
  have hsrc' : MapsTo α (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have htarget : MapsTo u (Icc a b) e.target := fun s hs ↦ e.map_source (hsrc' hs)
  have htime (s : ℝ) (hs : s ∈ Icc a b) : T - s ^ 2 ∈ J := by
    apply p.time_mem
    have hglobal := hsub hs
    have hsnonneg := (Real.sqrt_nonneg τ₁).trans hglobal.1
    constructor
    · simpa only [Real.sq_sqrt p.nonnegative] using
        (sq_le_sq₀ (Real.sqrt_nonneg τ₁) hsnonneg).mpr hglobal.1
    · simpa only [Real.sq_sqrt (p.nonnegative.trans p.ordered.le)] using
        (sq_le_sq₀ hsnonneg (Real.sqrt_nonneg τ₂)).mpr hglobal.2
  obtain ⟨E, hE⟩ := exists_regularizedEuler_extension_of_backward hM04 p hp
  let E' := restrictOpenVelocityExtension isOpen_Ioo isOpen_Ioo hsubo α E
  have hE' (s : ℝ) (hs : s ∈ Ioo a b) : regularizedLGeodesicEquation F T α (Ioo a b) E' s := by
    intro W
    rw [regularizedEulerResidual_restrictOpenVelocityExtension F T isOpen_Ioo
      isOpen_Ioo hsubo α E hs W]
    exact hE s (hsubo hs) W
  apply endpoint_chart_phase_contDiffOn F hM04 T x hab u (deriv u) hu hud hd htarget htime
  intro s hs
  have hmomentum := regularized_equation_chart_momentum F hM04 T isOpen_Ioo x α
    ((squarePath_regular p).mono hsubo) (hsrc.mono_left Ioo_subset_Icc_self) E' hs
    (backwardSquareTime_mem_interior hwindow p.nonnegative p.ordered hτ₂ (hsubo hs))
    (hE' s hs)
  rw [spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ (Icc_mem_nhds hs.1 hs.2) (htarget (Ioo_subset_Icc_self hs)),
    spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ (Icc_mem_nhds hs.1 hs.2) (htarget (Ioo_subset_Icc_self hs))]
  exact hmomentum

set_option maxHeartbeats 1000000 in
theorem squarePath_local_phase {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ s₀ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hp : IsBackwardLGeodesic F T τ₁ τ₂ p)
    (hs₀ : s₀ ∈ sqrtParameterInterval τ₁ τ₂) :
    ∃ (a b : ℝ) (x : M) (Pbar : ℝ → EuclideanSpace ℝ (Fin n)),
      a < b ∧ Real.sqrt τ₁ ≤ a ∧ b ≤ Real.sqrt τ₂ ∧ s₀ ∈ Icc a b ∧
      Icc a b ∈ 𝓝[sqrtParameterInterval τ₁ τ₂] s₀ ∧
      MapsTo (squareReparameterizedCurve p.curve) (Icc a b)
        (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      ContDiffOn ℝ ∞ (fun s ↦
        (extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve s), Pbar s)) (Icc a b) ∧
      EqOn Pbar (fun s ↦ chartMetricOperator F T x
        (s, extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve s))
        (deriv ((extChartAt (𝓡 n) x) ∘ squareReparameterizedCurve p.curve) s)) (Ioo a b) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt (fun r ↦
        (extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve r), Pbar r))
        (closedChartEulerPhase F T x (Icc a b) s
          (extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve s), Pbar s)) (Icc a b) s := by
  let A := Real.sqrt τ₁
  let B := Real.sqrt τ₂
  let α := squareReparameterizedCurve p.curve
  let x := α s₀
  have hAB : A < B := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  obtain ⟨γ, hγ, hγα⟩ := exists_continuous_squarePath_extension p
  have hnear : γ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∈ 𝓝 s₀ := by
    apply hγ.continuousAt.preimage_mem_nhds
    apply (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds
    rw [hγα hs₀]
    exact mem_chart_source _ _
  obtain ⟨l, r, ⟨hls, hsr⟩, hchart⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let l' := (l + s₀) / 2
  let r' := (s₀ + r) / 2
  let a := max A l'
  let b := min B r'
  have hll : l < l' := by dsimp only [l']; linarith
  have hls' : l' < s₀ := by dsimp only [l']; linarith
  have hsr' : s₀ < r' := by dsimp only [r']; linarith
  have hrr : r' < r := by dsimp only [r']; linarith
  have hAa : A ≤ a := le_max_left _ _
  have hbB : b ≤ B := min_le_left _ _
  have hab : a < b := by
    apply max_lt
    · exact lt_min hAB (lt_of_le_of_lt hs₀.1 hsr')
    · exact lt_min (lt_of_lt_of_le hls' hs₀.2) (hls'.trans hsr')
  have hsab : s₀ ∈ Icc a b :=
    ⟨max_le hs₀.1 hls'.le, le_min hs₀.2 hsr'.le⟩
  have hnhds : Icc a b ∈ 𝓝[sqrtParameterInterval τ₁ τ₂] s₀ := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Ioo l' r', Ioo_mem_nhds hls' hsr', ?_⟩
    intro s hs
    exact ⟨max_le hs.2.1 hs.1.1.le, le_min hs.2.2 hs.1.2.le⟩
  have hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    intro s hs
    have h := hchart ⟨hll.trans_le ((le_max_right _ _).trans hs.1),
      (hs.2.trans (min_le_right _ _)).trans_lt hrr⟩
    change γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source at h
    rwa [hγα ⟨hAa.trans hs.1, hs.2.trans hbB⟩] at h
  obtain ⟨Pbar, hsm, hag, hd⟩ := squarePath_chart_phase hM04 hwindow hcurvature hτ₂ p hp
    hab hAa hbB x hsrc
  exact ⟨a, b, x, Pbar, hab, hAa, hbB, hsab, hnhds, hsrc, hsm, hag, hd⟩

theorem squarePath_contMDiffOn_of_euler {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hp : IsBackwardLGeodesic F T τ₁ τ₂ p) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (squareReparameterizedCurve p.curve)
      (sqrtParameterInterval τ₁ τ₂) := by
  intro s hs
  obtain ⟨a, b, x, Pbar, _, _, _, hsab, hnhds, hsrc, hsm, _, _⟩ :=
    squarePath_local_phase hM04 hwindow hcurvature hτ₂ p hp hs
  let e := extChartAt (𝓡 n) x
  let α := squareReparameterizedCurve p.curve
  have hsrc' : MapsTo α (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have htarget : MapsTo (e ∘ α) (Icc a b) e.target :=
    fun r hr ↦ e.map_source (hsrc' hr)
  have hcomp := (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp
    hsm.fst.contMDiffOn htarget
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Icc a b) :=
    hcomp.congr (fun r hr ↦ (e.left_inv (hsrc' hr)).symm)
  exact (hα s hsab).mono_of_mem_nhdsWithin hnhds

end PoincareConjecture.M08
