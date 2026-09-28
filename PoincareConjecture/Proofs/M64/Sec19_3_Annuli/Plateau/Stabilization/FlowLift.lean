import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.CurveLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem auxiliaryCircle_c2ShrinkingCurve
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    {c : ℝ → ℝ → M} {J : Set ℝ} (hc : M63C2ShrinkingCurveOn F c J) :
    M63C2ShrinkingCurveOn P.flow (fun x t => auxiliaryCircleSection P q (c x t)) J := by
  let d := fun x t => auxiliaryCircleSection P q (c x t)
  have he := auxiliaryCircle_section_contMDiff P q
  have hdiff (t : ℝ) (ht : t ∈ J) (x : ℝ) :
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t) x :=
    (hc.spatial_regular t ht).mdifferentiableAt (by norm_num)
  have hpush := he.continuous_tangentMap (by simp)
  have hvel := hpush.comp_continuousOn hc.velocity_continuous
  have hcurv := hpush.comp_continuousOn hc.curvature_continuous
  refine
    { domain_subset := hc.domain_subset
      periodic := fun t ht x => ?_
      spatial_regular := fun t ht =>
        (he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
          (hc.spatial_regular t ht)
      joint_c1 := (he.of_le (by simp)).comp_contMDiffOn hc.joint_c1
      immersed := fun t ht x hzero => ?_
      continuous := he.continuous.comp_continuousOn hc.continuous
      velocity_continuous := hvel.congr (fun z hz => ?_)
      curvature_continuous := hcurv.congr (fun z hz => ?_)
      equation := fun t ht x => ?_ }
  · change auxiliaryCircleSection P q (c (x + curvePeriod) t) =
      auxiliaryCircleSection P q (c x t)
    exact congrArg (auxiliaryCircleSection P q) (hc.periodic t ht x)
  · apply hc.immersed t ht x
    have hs := auxiliaryCircle_curveVelocity_split P q (hdiff t ht x)
    change curveVelocity (auxiliaryCircleSection P q ∘ fun y => c y t) x = 0 at hzero
    rw [hzero, map_zero] at hs
    exact (congrArg Prod.fst hs).symm
  · change (⟨d z.1 z.2, curveVelocity (fun y => d y z.2) z.1⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point) = _
    apply congrArg (fun v => (⟨d z.1 z.2, v⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point))
    exact auxiliaryCircle_curveVelocity_eq P q (hdiff z.2 hz.2 z.1)
  · change (⟨d z.1 z.2, m62CurvatureVector P.flow d z.2 z.1⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point) = _
    apply congrArg (fun v => (⟨d z.1 z.2, v⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point))
    exact auxiliaryCircle_curvatureVector_eq P q c z.2 (hc.spatial_regular z.2 hz.2)
      (hc.immersed z.2 hz.2) z.1
  · have hmem : (x, t) ∈ univ ×ˢ interior J := ⟨mem_univ _, ht⟩
    have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun s : ℝ => (x, s)) t :=
      ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
    have hct : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => c x s) t :=
      (((hc.joint_c1 (x, t) hmem).contMDiffAt
        ((isOpen_univ.prod isOpen_interior).mem_nhds hmem)).mdifferentiableAt
          (by norm_num)).comp t htime
    change curveVelocity (auxiliaryCircleSection P q ∘ fun s => c x s) t = _
    rw [auxiliaryCircle_curveVelocity_eq P q hct, hc.equation t ht x]
    exact (auxiliaryCircle_curvatureVector_eq P q c t
      (hc.spatial_regular t (interior_subset ht))
      (hc.immersed t (interior_subset ht)) x).symm

end PoincareConjecture.M64
