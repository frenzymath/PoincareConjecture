import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductIdentities
import PoincareConjecture.Proofs.M62.Lemma0_2_NormalizedFields
import PoincareConjecture.Statements.M62CurveEvolution











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem hasDerivAt_slope {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    HasDerivAt (fun s => m62Slope P c s x)
      (m62ArcSecondDerivative P.flow c t (m62Slope P c t) x +
        (m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x) *
          m62Slope P c t x) t := by
  let := P.charts.chartedSpace
  let B := P.charts.circleUnit
  have hP := circleProduct_identities P
  have hclosed := Ioo_subset_Icc_self ht
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hB (p : P.charts.Point) : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent
      (T% B) p := (hP.circle_unit_smooth p).mdifferentiableAt (by simp)
  have hspace (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun z => c z t) y :=
    (hc.spatial_regular t hclosed y).mdifferentiableAt (by norm_num)
  have hparallel (y : ℝ) :
      rampHorizontalCovariantDerivative (P.flow.connection t) (fun z => c z t)
        (fun z => B (c z t)) y = 0 := by
    rw [pullback_ambient_field (P.flow.connection t) (hspace y) B (hB (c y t))]
    exact hP.circle_parallel t (c y t) _
  have hfirst (y : ℝ) : m62ArcDerivative P.flow c t (m62Slope P c t) y =
      (P.flow.metric t).inner (c y t) (m62CurvatureVector P.flow c t y) (B (c y t)) := by
    have hp := hasDerivAt_metric_pairing (P.flow.connection t) (hspace y)
      ((unitTangent_contMDiff P.flow c hc hclosed y).mdifferentiableAt (by simp))
      ((hB (c y t)).comp y (hspace y))
    change HasDerivAt (m62Slope P c t) _ y at hp
    unfold m62ArcDerivative
    rw [hp.deriv, hparallel]
    simp only [map_zero, add_zero, m62CurvatureVector, m62SpatialDerivative,
      map_smul, smul_apply, smul_eq_mul]
  have hH : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
      (fun y => (⟨c y t, m62CurvatureVector P.flow c t y⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point)) x := by
    have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun y : ℝ => (y, t)) x :=
      (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
    exact (((curvature_joint_contMDiff P.flow c hc).contMDiffAt
      (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp x hs
  have hsecond : m62ArcSecondDerivative P.flow c t (m62Slope P c t) x =
      (P.flow.metric t).inner (c x t)
        (m62SpatialDerivative P.flow c t (m62CurvatureVector P.flow c t) x) (B (c x t)) := by
    have hp := hasDerivAt_metric_pairing (P.flow.connection t) (hspace x) hH
      ((hB (c x t)).comp x (hspace x))
    unfold m62ArcSecondDerivative
    rw [funext hfirst]
    unfold m62ArcDerivative
    rw [hp.deriv, hparallel]
    simp only [map_zero, add_zero, m62SpatialDerivative, map_smul, smul_apply, smul_eq_mul]
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun s : ℝ => (x, s)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hcurve := ((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
    (by simp)).comp t htime
  change MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun s : ℝ => c x s) t at hcurve
  have hS := (((unitTangent_joint_contMDiff P.flow c hc).contMDiffAt
    (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp t htime
  change MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
    (fun s : ℝ => (⟨c x s, spatialUnitTangent P.flow c s x⟩ :
      TangentBundle (𝓡 (n + 1)) P.charts.Point)) t at hS
  have hparallel_time :
      rampHorizontalCovariantDerivative (P.flow.connection t) (fun s => c x s)
        (fun s => B (c x s)) t = 0 := by
    rw [pullback_ambient_field (P.flow.connection t) hcurve B (hB (c x t))]
    exact hP.circle_parallel t (c x t) _
  have hflow := hasDerivAt_flow_metric_pairing P.flow
    (γ := fun s => c x s) (Y := fun s => spatialUnitTangent P.flow c s x)
    (Z := fun s => B (c x s)) ht hcurve hS ((hB (c x t)).comp t hcurve)
  apply hflow.congr_deriv
  rw [hP.circle_ricci, hparallel_time, unitTangent_time_derivative P.flow c hc ht x]
  simp only [mul_zero, zero_add, map_zero, add_zero, map_add, add_apply,
    map_smul, smul_apply, smul_eq_mul]
  rw [hsecond]
  change _ + (_ + _) * m62Slope P c t x = _ + (_ + _) * m62Slope P c t x
  ring

end PoincareConjecture.M62
