import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRegularity
import PoincareConjecture.Proofs.M62.Lemma0_1_SpeedEvolution









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem unitTangent_joint_contMDiff (hc : M62ShrinkingCurve F c) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ => (⟨c z.1 z.2, spatialUnitTangent F c z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Ioo a b) := by
  have hX := spatial_velocity_joint_contMDiff F c hc
  have hv := ((speed_joint_contDiffOn F c hc).inv
    (fun z hz => (speed_pos F c hc (Ioo_subset_Icc_self hz.2) z.1).ne')).contMDiffOn
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hc.joint_smooth.contMDiffAt (hopen.mem_nhds hz), ?_⟩
  have hcoord := (hv.contMDiffAt (hopen.mem_nhds hz)).smul
    (Bundle.contMDiffAt_totalSpace.mp (hX.contMDiffAt (hopen.mem_nhds hz))).2
  apply hcoord.congr_of_eventuallyEq
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (c z.1 z.2)
  have hnear : ∀ᶠ w in 𝓝 z, c w.1 w.2 ∈ e.baseSet :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hz)).continuousAt
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (c z.1 z.2)))
  filter_upwards [hnear] with w hw
  change (e ⟨c w.1 w.2, (curveSpeed F c w.2 w.1)⁻¹ •
      curveVelocity (fun s => c s w.2) w.1⟩).2 =
    (curveSpeed F c w.2 w.1)⁻¹ • (e ⟨c w.1 w.2, curveVelocity (fun s => c s w.2) w.1⟩).2
  simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hw] using
    (e.continuousLinearMapAt ℝ (c w.1 w.2)).map_smul
      (curveSpeed F c w.2 w.1)⁻¹ (curveVelocity (fun s => c s w.2) w.1)



theorem spatialDerivative_joint_contMDiff [T2Space M]
    (hc : M62ShrinkingCurve F c)
    (Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M))
      (Set.univ ×ˢ Set.Ioo a b)) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ => (⟨c z.1 z.2,
        m62SpatialDerivative F c z.2 (fun s => Y (s, z.2)) z.1⟩ :
        TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Ioo a b) := by
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hD := flow_pullback_space_smooth F c Y hopen
    (fun z hz => by simpa only [interior_Icc] using hz.2) hc.joint_smooth hY
  have hv := ((speed_joint_contDiffOn F c hc).inv
    (fun z hz => (speed_pos F c hc (Ioo_subset_Icc_self hz.2) z.1).ne')).contMDiffOn
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hc.joint_smooth.contMDiffAt (hopen.mem_nhds hz), ?_⟩
  have hcoord := (hv.contMDiffAt (hopen.mem_nhds hz)).smul
    (Bundle.contMDiffAt_totalSpace.mp (hD.contMDiffAt (hopen.mem_nhds hz))).2
  apply hcoord.congr_of_eventuallyEq
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (c z.1 z.2)
  have hnear : ∀ᶠ w in 𝓝 z, c w.1 w.2 ∈ e.baseSet :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hz)).continuousAt
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (c z.1 z.2)))
  filter_upwards [hnear] with w hw
  change (e ⟨c w.1 w.2, (curveSpeed F c w.2 w.1)⁻¹ •
      rampHorizontalCovariantDerivative (F.connection w.2) (fun s => c s w.2)
        (fun s => Y (s, w.2)) w.1⟩).2 =
    (curveSpeed F c w.2 w.1)⁻¹ • (e ⟨c w.1 w.2,
      rampHorizontalCovariantDerivative (F.connection w.2) (fun s => c s w.2)
        (fun s => Y (s, w.2)) w.1⟩).2
  simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hw] using
    (e.continuousLinearMapAt ℝ (c w.1 w.2)).map_smul (curveSpeed F c w.2 w.1)⁻¹
      (rampHorizontalCovariantDerivative (F.connection w.2) (fun s => c s w.2)
        (fun s => Y (s, w.2)) w.1)



theorem normalization_coefficient_contDiffOn (hc : M62ShrinkingCurve F c) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
      m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1)
      (Set.univ ×ˢ Set.Ioo a b) := by
  let v : ℝ × ℝ → ℝ := fun z => curveSpeed F c z.2 z.1
  have hv : ContDiffOn ℝ ∞ v (univ ×ˢ Ioo a b) := speed_joint_contDiffOn F c hc
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hvinv := hv.inv (fun z hz => (speed_pos F c hc (Ioo_subset_Icc_self hz.2) z.1).ne')
  apply ((M08.coordinatePartialU_contDiffOn hopen v hv).neg.mul hvinv).congr
  intro z hz
  have hd := (M08.coordinateSlice_snd_hasDerivAt v
    ((hv.contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp))).unique
      (hasDerivAt_speed F c hc hz.2 z.1)
  change m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1 =
    -(fderiv ℝ v z (0, 1)) * (v z)⁻¹
  rw [hd]
  dsimp only [v]
  have hnonzero := (speed_pos F c hc (Ioo_subset_Icc_self hz.2) z.1).ne'
  field_simp



theorem unitTangent_time_derivative (hc : M62ShrinkingCurve F c)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    rampHorizontalCovariantDerivative (F.connection t) (fun r => c x r)
      (fun r => spatialUnitTangent F c r x) t =
      m62SpatialDerivative F c t (m62CurvatureVector F c t) x +
        (m62TangentRicci F c t x + m62CurvatureSquared F c t x) •
          spatialUnitTangent F c t x := by
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (x, r)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hX := ((spatial_velocity_joint_contMDiff F c hc).contMDiffAt
    (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)
  have hv := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hvinv : HasDerivAt (fun r => (curveSpeed F c r x)⁻¹)
      ((m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
        (curveSpeed F c t x)⁻¹) t := by
    apply ((hasDerivAt_speed F c hc ht x).inv hv).congr_deriv
    field_simp
  have hcomm := pullback_velocity_commute (F.connection t) c hopen hc.joint_smooth hmem
  have heq : (fun s => curveVelocity (fun r => c s r) t) = m62CurvatureVector F c t :=
    funext (hc.equation t ht)
  rw [heq] at hcomm
  change rampHorizontalCovariantDerivative (F.connection t) (fun r => c x r)
    (fun r => (curveSpeed F c r x)⁻¹ • curveVelocity (fun s => c s r) x) t = _
  rw [pullback_smul (F.connection t) hvinv
    (by simpa only [Function.comp_def] using hX.comp t htime), hcomm]
  simp only [m62SpatialDerivative, spatialUnitTangent, mul_smul]
  exact add_comm _ _

end PoincareConjecture.M62
