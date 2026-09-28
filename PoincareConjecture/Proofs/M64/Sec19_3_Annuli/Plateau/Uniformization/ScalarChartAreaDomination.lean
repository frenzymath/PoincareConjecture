import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarChartAreaLimit












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)





theorem scalarC1_composed_area_bound
    (g : RiemannianMetric n M) {f : E → M} {U Q : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 m) (𝓡 n) 1 f U) (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (L : ℝ≥0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Plane → E), LipschitzWith L u →
      ∀ x : Plane, u x ∈ Q → DifferentiableAt ℝ u x →
        m60AreaDensity g (f ∘ u) x ≤ C := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let B := fun p : E × (E × E) =>
    g.inner (f p.1) (mfderiv (𝓡 m) (𝓡 n) f p.1 p.2.1)
      (mfderiv (𝓡 m) (𝓡 n) f p.1 p.2.2)
  let T := Q ×ˢ (Metric.closedBall (0 : E) L ×ˢ Metric.closedBall (0 : E) L)
  have hT : IsCompact T := hQ.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hB : ContinuousOn B (U ×ˢ univ) := M60.continuousOn_pullback_inner hU hf
  obtain ⟨C, hC⟩ := hT.bddAbove_image ((hB.mono
    (fun _ hp => ⟨hQU hp.1, mem_univ _⟩)).norm)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu x hx hdx
  have hnorm (i : Fin 2) :
      fderiv ℝ u x (EuclideanSpace.single i 1) ∈ Metric.closedBall (0 : E) L := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ((fderiv ℝ u x).le_opNorm _).trans (by
      simpa using (norm_fderiv_le_of_lipschitz ℝ hu : ‖fderiv ℝ u x‖ ≤ (L : ℝ)))
  have hdiag (i : Fin 2) : m60AreaGram g (f ∘ u) x i i ≤ max C 0 := by
    have hfd := (hf.contMDiffAt (hU.mem_nhds (hQU hx))).mdifferentiableAt one_ne_zero
    have hb := hC (mem_image_of_mem (fun p => ‖B p‖)
      (show (u x, fderiv ℝ u x (EuclideanSpace.single i 1),
        fderiv ℝ u x (EuclideanSpace.single i 1)) ∈ T from ⟨hx, hnorm i, hnorm i⟩))
    have hb' : |B (u x, fderiv ℝ u x (EuclideanSpace.single i 1),
        fderiv ℝ u x (EuclideanSpace.single i 1))| ≤ C := by
      simpa only [Real.norm_eq_abs] using hb
    have hle := (le_abs_self (B (u x, fderiv ℝ u x (EuclideanSpace.single i 1),
      fderiv ℝ u x (EuclideanSpace.single i 1)))).trans (hb'.trans (le_max_left C 0))
    simpa only [m60AreaGram, mfderiv_comp x hfd
      (mdifferentiableAt_iff_differentiableAt.mpr hdx), mfderiv_eq_fderiv,
      EuclideanSpace.basisFun_apply, ContinuousLinearMap.comp_apply, B,
      Function.comp_apply] using! hle
  apply (m60AreaDensity_le_energyDensity g (f ∘ u) x).trans
  simp only [m60EnergyDensity, Matrix.trace_fin_two]
  linarith [hdiag 0, hdiag 1]





theorem scalarC1_composed_area_integrable
    (g : RiemannianMetric n M) {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 m) (𝓡 n) 1 f U)
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {K : Set Plane} (hK : IsCompact K) (huK : MapsTo u K U) :
    IntegrableOn (m60AreaDensity g (f ∘ u)) K := by
  have hQ : IsCompact (u '' K) := hK.image hu.continuous
  have hQU : u '' K ⊆ U := by rintro _ ⟨x, hx, rfl⟩; exact huK hx
  obtain ⟨C, -, hbound⟩ := scalarC1_composed_area_bound g hU hf hQ hQU L
  let O := u ⁻¹' U
  have hO : IsOpen O := hU.preimage hu.continuous
  have hcont : ContinuousOn (f ∘ u) O :=
    hf.continuousOn.comp hu.continuous.continuousOn (fun _ hp => hp)
  have hKO : K ⊆ O := huK
  have hm := (m60AreaDensity_aestronglyMeasurableOn g hO hcont).mono_measure
    (Measure.restrict_mono hKO le_rfl)
  have hCI : Integrable (fun _ : Plane => C) (volume.restrict K) :=
    continuousOn_const.integrableOn_compact hK
  apply hCI.mono' hm
  filter_upwards [ae_restrict_mem hK.measurableSet,
    ae_restrict_of_ae (hu.ae_differentiableAt (μ := volume))] with x hx hdx
  rw [Real.norm_of_nonneg (m60AreaDensity_nonneg _ _ _)]
  exact hbound u hu x (mem_image_of_mem u hx) hdx





theorem scalarC1_composed_area_integral_tendsto
    (g : RiemannianMetric n M) {f : E → M} {U Q : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 m) (𝓡 n) 1 f U) (hQ : IsCompact Q) (hQU : Q ⊆ U)
    {K : Set Plane} (hK : IsCompact K)
    {u : Plane → E} {v : ℕ → Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) (hv : ∀ j, LipschitzWith L (v j))
    (huQ : MapsTo u K Q) (hvQ : ∀ j, MapsTo (v j) K Q)
    (hval : ∀ x ∈ K, Tendsto (fun j => v j x) atTop (𝓝 (u x)))
    (hcol : ∀ᵐ x ∂volume, ∀ i : Fin 2, Tendsto
      (fun j => fderiv ℝ (v j) x (EuclideanSpace.single i 1)) atTop
      (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1)))) :
    Tendsto (fun j => ∫ x in K, m60AreaDensity g (f ∘ v j) x) atTop
      (𝓝 (∫ x in K, m60AreaDensity g (f ∘ u) x)) := by
  obtain ⟨C, -, hbound⟩ := scalarC1_composed_area_bound g hU hf hQ hQU L
  have hdv : ∀ᵐ x ∂volume, ∀ j, DifferentiableAt ℝ (v j) x :=
    ae_all_iff.mpr (fun j => (hv j).ae_differentiableAt (μ := volume))
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro j
    let O := (v j) ⁻¹' U
    have hO : IsOpen O := hU.preimage (hv j).continuous
    have hcont : ContinuousOn (f ∘ v j) O :=
      hf.continuousOn.comp (hv j).continuous.continuousOn (fun _ hp => hp)
    have hKO : K ⊆ O := fun _ hx => hQU (hvQ j hx)
    exact (m60AreaDensity_aestronglyMeasurableOn g hO hcont).mono_measure
      (Measure.restrict_mono hKO le_rfl)
  · exact continuousOn_const.integrableOn_compact hK
  · intro j
    filter_upwards [ae_restrict_mem hK.measurableSet,
      ae_restrict_of_ae hdv] with x hx hdx
    rw [Real.norm_of_nonneg (m60AreaDensity_nonneg _ _ _)]
    exact hbound (v j) (hv j) x (hvQ j hx) (hdx j)
  · filter_upwards [ae_restrict_mem hK.measurableSet,
      ae_restrict_of_ae (hu.ae_differentiableAt (μ := volume)),
      ae_restrict_of_ae hdv, ae_restrict_of_ae hcol] with x hx hdu hdv hdc
    exact scalarC1_composed_area_tendsto g hU hf hdu hdv
      (hQU (huQ hx)) (fun j => hQU (hvQ j hx)) (hval x hx) hdc

end PoincareConjecture.M64Uniformization
