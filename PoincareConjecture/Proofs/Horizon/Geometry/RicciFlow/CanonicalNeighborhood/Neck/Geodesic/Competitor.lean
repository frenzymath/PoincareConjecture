import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Chord
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Comparison


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

theorem model_path_smooth
    {z w : RoundCylinderSpace} {σ : ℝ → UnitTwoSphere}
    (hσ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 σ (Icc (0 : ℝ) 1)) :
    ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1
      (fun t ↦ (σ t, z.2 + t * (w.2 - z.2))) (Icc (0 : ℝ) 1) := by
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (fun t : ℝ ↦ z.2 + t * (w.2 - z.2)) := by
    have hc : ContDiff ℝ 1 (fun t : ℝ ↦ z.2 + t * (w.2 - z.2)) := by fun_prop
    exact hc.contMDiff
  exact hσ.prodMk hline.contMDiffOn

theorem model_path_mem
    {z w : RoundCylinderSpace} {σ : ℝ → UnitTwoSphere}
    {ε : ℝ} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (hw : w.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    MapsTo (fun t ↦ (σ t, z.2 + t * (w.2 - z.2))) (Icc (0 : ℝ) 1)
      (Set.univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) := by
  intro t ht
  refine ⟨mem_univ _, ?_⟩
  have hseg : z.2 + t • (w.2 - z.2) ∈ Ioo (-(ε⁻¹ : ℝ)) (ε⁻¹ : ℝ) := by
    apply (convex_Ioo (𝕜 := ℝ) (-(ε⁻¹ : ℝ)) (ε⁻¹ : ℝ)).segment_subset hz hw
    rw [segment_eq_image' (𝕜 := ℝ) z.2 w.2]
    exact ⟨t, ht, rfl⟩
  simpa [smul_eq_mul] using hseg

theorem model_path_length_le
    {z w : RoundCylinderSpace} {σ : ℝ → UnitTwoSphere}
    (hσ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 σ (Icc (0 : ℝ) 1))
    (hσlen : (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).pathELength σ 0 1 ≤
      ENNReal.ofReal (Real.pi + 1)) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    roundCylinderMetric.pathELength
        (roundCylinderModelDiffeomorph ∘
          (fun t ↦ (σ t, z.2 + t * (w.2 - z.2)))) 0 1 ≤
      ENNReal.ofReal (Real.sqrt 2 * (Real.pi + 1)) +
        ENNReal.ofReal |z.2 - w.2| := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let η : ℝ → RoundCylinderSpace := fun t ↦ (σ t, z.2 + t * (w.2 - z.2))
  let e := roundCylinderModelDiffeomorph
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1 η (Icc 0 1) := by
    exact model_path_smooth hσ
  rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm]
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))]
  let s : ℝ → ℝ := fun t ↦
    (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).tangentNorm
      (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1)
  let a : ℝ≥0∞ := ENNReal.ofReal |z.2 - w.2|
  calc
    (∫⁻ (u : ℝ) in Ioo 0 1,
        ENNReal.ofReal (roundCylinderMetric.tangentNorm ((e ∘ η) u)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (e ∘ η) u 1))) ≤
        ∫⁻ (u : ℝ) in Ioo 0 1,
          (a + ENNReal.ofReal (Real.sqrt 2 * s u)) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t ht
      have hηt := hη.contMDiffAt (Icc_mem_nhds ht.1 ht.2)
      have het := e.contMDiff.mdifferentiable (by simp) (η t)
      have hchain := mfderiv_comp t het (hηt.mdifferentiableAt one_ne_zero)
      rw [hchain]
      have hline : ContDiff ℝ 1 (fun u : ℝ ↦ z.2 + u * (w.2 - z.2)) := by
        fun_prop
      have hσt := (hσ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
      have hline_t := hline.contMDiff.mdifferentiableAt (x := t) one_ne_zero
      change ENNReal.ofReal (roundCylinderMetric.tangentNorm (e (η t))
        ((mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (η t))
          ((mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t) 1))) ≤ _
      change ENNReal.ofReal (Real.sqrt (roundCylinderMetric.inner (e (η t))
        ((mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (η t))
          ((mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t) 1))
        ((mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (η t))
          ((mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t) 1)))) ≤ _
      dsimp [e]
      rw [roundCylinderMetric_inner]
      simp only [EvolvingRoundCylinderMetric, sub_zero, one_mul]
      have hfst := mfderiv_comp_apply t (mdifferentiableAt_fst)
        (hηt.mdifferentiableAt one_ne_zero) (1 : TangentSpace 𝓘(ℝ, ℝ) t)
      have hsnd := mfderiv_comp_apply t (mdifferentiableAt_snd)
        (hηt.mdifferentiableAt one_ne_zero) (1 : TangentSpace 𝓘(ℝ, ℝ) t)
      simp only [mfderiv_fst, mfderiv_snd] at hfst hsnd
      simp only [Function.comp_apply] at hfst hsnd
      have hηfst : Prod.fst ∘ η = σ := by funext u; rfl
      have hηsnd : Prod.snd ∘ η =
          (fun u : ℝ ↦ z.2 + u * (w.2 - z.2)) := by funext u; rfl
      rw [hηfst] at hfst
      rw [hηsnd] at hsnd
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1 = ((mfderiv 𝓘(ℝ, ℝ)
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t) 1).1 at hfst
      change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun u : ℝ ↦ z.2 + u * (w.2 - z.2)) t) 1 =
        ((mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t) 1).2 at hsnd
      rw [← hfst, ← hsnd]
      have hline_deriv :
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
            (fun u : ℝ ↦ z.2 + u * (w.2 - z.2)) t) 1 = w.2 - z.2 := by
        rw [mfderiv_eq_fderiv]
        have hd : HasDerivAt (fun u : ℝ ↦ z.2 + u * (w.2 - z.2))
            (w.2 - z.2) t := by
          convert (hasDerivAt_const t z.2).add
            ((hasDerivAt_id t).mul_const (w.2 - z.2)) using 1
          all_goals try rfl
          all_goals simp
        change (fderiv ℝ (fun u : ℝ ↦ z.2 + u * (w.2 - z.2)) t) 1 = _
        rw [fderiv_apply_one_eq_deriv]
        exact hd.deriv
      rw [hline_deriv]
      dsimp [η]
      rw [← PoincareConjecture.RiemannianMetric.euclideanMetric_inner]
      rw [← Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner]
      dsimp [s, a, RiemannianMetric.tangentNorm]
      have hq : 0 ≤
          (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
            (σ t) ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)
            ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1) := by
        rw [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner]
        rw [PoincareConjecture.RiemannianMetric.euclideanMetric_inner]
        exact real_inner_self_nonneg
      have hreal :
          Real.sqrt (2 *
              (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
                (σ t) ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)
                ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1) + (w.2 - z.2) ^ 2) ≤
            Real.sqrt 2 * Real.sqrt
              ((Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
                (σ t) ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)
                ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)) + |z.2 - w.2| := by
        have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
          rw [Real.sq_sqrt]
          norm_num
        have hsq : (Real.sqrt
              ((Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
                (σ t) ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)
                ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1))) ^ 2 =
            (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
              (σ t) ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)
              ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1) := by
          rw [Real.sq_sqrt hq]
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · have hcross : 0 ≤ 2 * Real.sqrt 2 * Real.sqrt
              ((Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
                (σ t) ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)
                ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)) * |z.2 - w.2| := by
            positivity
          nlinarith [sq_abs (z.2 - w.2), abs_nonneg (z.2 - w.2), hcross,
            Real.sqrt_nonneg
              ((Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner
                (σ t) ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)
                ((mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) 1)),
            Real.sqrt_nonneg 2]
      rw [← ENNReal.ofReal_add (abs_nonneg (z.2 - w.2))
        (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (by simpa [abs_sub_comm, add_comm, pow_two] using hreal)
    _ = (∫⁻ (u : ℝ) in Ioo 0 1, ENNReal.ofReal (Real.sqrt 2 * s u)) +
        (∫⁻ (_ : ℝ) in Ioo 0 1, a) := by
      rw [show (fun u : ℝ ↦ a + ENNReal.ofReal (Real.sqrt 2 * s u)) =
          (fun u ↦ ENNReal.ofReal (Real.sqrt 2 * s u) + a) by
            funext u; ac_rfl]
      rw [lintegral_add_right' (μ := volume.restrict (Ioo (0 : ℝ) 1)) _
        measurable_const.aemeasurable]
    _ = ENNReal.ofReal (Real.sqrt 2) *
          (∫⁻ (u : ℝ) in Ioo 0 1, ENNReal.ofReal (s u)) +
        ENNReal.ofReal |z.2 - w.2| := by
      rw [show (fun u : ℝ ↦ ENNReal.ofReal (Real.sqrt 2 * s u)) =
          (fun u ↦ ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (s u)) by
            funext u; rw [ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [setLIntegral_const]
      simp
      rfl
    _ ≤ ENNReal.ofReal (Real.sqrt 2 * (Real.pi + 1)) +
        ENNReal.ofReal |z.2 - w.2| := by
      have hslen' : (∫⁻ (u : ℝ) in Ioo 0 1, ENNReal.ofReal (s u)) ≤
          ENNReal.ofReal (Real.pi + 1) := by
        have hσlen' := hσlen
        rw [PoincareConjecture.RiemannianMetric.pathELength_eq_lintegral_tangentNorm] at hσlen'
        rw [← Measure.restrict_congr_set
          (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))] at hσlen'
        simpa [s] using hσlen'
      calc
        (ENNReal.ofReal (Real.sqrt 2) *
            (∫⁻ (u : ℝ) in Ioo 0 1, ENNReal.ofReal (s u))) +
            ENNReal.ofReal |z.2 - w.2| ≤
            (ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (Real.pi + 1)) +
              ENNReal.ofReal |z.2 - w.2| :=
          add_le_add
            (mul_le_mul_of_nonneg_left hslen'
              (bot_le : (⊥ : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt 2))) le_rfl
        _ = ENNReal.ofReal (Real.sqrt 2 * (Real.pi + 1)) +
              ENNReal.ofReal |z.2 - w.2| := by
          rw [ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]


end PoincareConjecture.EpsilonNeck
