import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationPullback











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace PoincareConjecture.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] {a b : ℝ}




theorem curvature_contMDiffOn (F : RicciFlow 3 M (Icc a b))
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hTime : ∀ z ∈ U, z.2.2 ∈ Icc a b)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U)
    (himm : ∀ z ∈ U,
      curveVelocity (n := 3) (fun x => c (z.1, (x, z.2.2))) z.2.1 ≠ 0) :
    ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z,
        m62CurvatureVector F (fun x t => c (z.1, (x, t))) z.2.2 z.2.1⟩ :
          TangentBundle (𝓡 3) M)) U := by
  have hY := unitTangent_contMDiffOn F c U hU hTime hc himm
  have hD := pullback_angular_contMDiffOn F c U hU hTime hc _ hY
  have hv := (speed_contDiffOn F c U hU hTime hc himm).inv
    (fun z hz => (Real.sqrt_pos.mpr ((F.metric z.2.2).pos _ _ (himm z hz))).ne')
  exact smul_field_contMDiffOn c U hU hc _ hv _ hD




theorem residual_continuousOn (F : RicciFlow 3 M (Icc a b))
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hTime : ∀ z ∈ U, z.2.2 ∈ Icc a b)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U)
    (himm : ∀ z ∈ U,
      curveVelocity (n := 3) (fun x => c (z.1, (x, z.2.2))) z.2.1 ≠ 0) :
    ContinuousOn (fun z => (F.metric z.2.2).tangentNorm (c z)
      (curveVelocity (n := 3) (fun t => c (z.1, (z.2.1, t))) z.2.2 -
        m62CurvatureVector F (fun x t => c (z.1, (x, t))) z.2.2 z.2.1)) U := by
  let V := fun z : P × (ℝ × ℝ) =>
    curveVelocity (n := 3) (fun t => c (z.1, (z.2.1, t))) z.2.2
  let H := fun z : P × (ℝ × ℝ) =>
    m62CurvatureVector F (fun x t => c (z.1, (x, t))) z.2.2 z.2.1
  have hV := time_velocity_contMDiffOn c U hU hc
  have hH := curvature_contMDiffOn F c U hU hTime hc himm
  have hVV := (metric_pairing_contDiffOn F c U hTime hc V V hV hV).continuousOn
  have hVH := (metric_pairing_contDiffOn F c U hTime hc V H hV hH).continuousOn
  have hHV := (metric_pairing_contDiffOn F c U hTime hc H V hH hV).continuousOn
  have hHH := (metric_pairing_contDiffOn F c U hTime hc H H hH hH).continuousOn
  apply (((hVV.sub hVH).sub hHV).add hHH).sqrt.congr
  intro z _
  change Real.sqrt ((F.metric z.2.2).inner (c z) (V z - H z) (V z - H z)) = _
  congr 1
  change (F.metric z.2.2).inner (c z) (V z - H z) (V z - H z) =
    (F.metric z.2.2).inner (c z) (V z) (V z) -
      (F.metric z.2.2).inner (c z) (V z) (H z) -
      (F.metric z.2.2).inner (c z) (H z) (V z) +
      (F.metric z.2.2).inner (c z) (H z) (H z)
  simp only [map_sub, sub_apply]
  ring

end PoincareConjecture.M65Perturbation
