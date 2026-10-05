import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Neck.NeckLaplacian
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Scalar.ScalarSign
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.Extension.TerminalPinching
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Formulas.ScalarEvolutionTransportRicci
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Actual scalar evolution along a compatible generalized-flow cylinder

Morgan--Tian equation (3.7), printed p. 41, Definitions 3.36-3.40,
pp. 60-61, and Claim 11.35, pp. 289-291. The original ordinary box
computes the retained slice numerator, and the actual clock contributes
the second normalization factor without extending a time interval.

The M12 GeneralizedBoxMetric declarations `originalBoxMetric_eq` and
`originalBoxMetric` identify precisely the frozen ordinary box metric
used here. Eligible M14 `ricciNormSq_eq_of_local_isometry` supplies its
quadratic term. Read-only M44/CylinderRicciFlow `scalar_eq` and
`scalar_evolution_eq` in Lemma16_8_CylinderCurvature are normalization
templates only. This proof uses the supplied M04 theory, the frozen
vertical compatibility, and Mathlib's within-domain chain rule directly.
Derivation: `claim11_35-neck-scalar-evolution.md`, sections 4-6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M32

/-- An actual ordinary box computes the retained slice scalar Laplacian.
Source: equation (3.7), p. 41, Remark 3.37, p. 60, and Claim 11.35,
printed pp. 289-291. -/
theorem box_scalarLaplacian_pullback (F : GeneralizedRicciFlowData.{u})
    (b : F.box_index) (t : ℝ) (ht : t ∈ (F.box b).interval)
    (x : (F.box b).carrier.carrier) :
    ((F.box b).flow.connection t).laplacian ((F.box b).flow.connection t).scalarCurvature x =
      (F.connection t).laplacian (F.connection t).scalarCurvature
        ((F.box b).forward t ht x) := by
  simpa only [one_pow, div_one] using scalarLaplacian_eq_of_local_homothety
    ((F.box b).flow.connection t) (F.connection t) (by norm_num : (0 : ℝ) < 1)
    isOpen_univ ((F.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => by simpa only [one_mul] using ((F.box b).metric_pullback t ht y v w).symm)
    (mem_univ x)

/-- The full ordinary-box scalar evolution numerator agrees with the
actual slice numerator. Source: equation (3.7), p. 41, Remark 3.37,
p. 60, and Claim 11.35, printed pp. 289-291. -/
theorem box_scalarEvolution_pullback (F : GeneralizedRicciFlowData.{u})
    (b : F.box_index) (t : ℝ) (ht : t ∈ (F.box b).interval)
    (x : (F.box b).carrier.carrier) :
    ((F.box b).flow.connection t).laplacian ((F.box b).flow.connection t).scalarCurvature x +
        2 * ((F.box b).flow.connection t).ricciNormSq x =
      (F.connection t).laplacian (F.connection t).scalarCurvature
          ((F.box b).forward t ht x) +
        2 * (F.connection t).ricciNormSq ((F.box b).forward t ht x) := by
  have hric := M14.ricciNormSq_eq_of_local_isometry
    ((F.box b).flow.connection t) (F.connection t) isOpen_univ
    ((F.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => ((F.box b).metric_pullback t ht y v w).symm) (mem_univ x)
  rw [box_scalarLaplacian_pullback F b t ht x, hric]

/-- The actual scalar divided by the cylinder scale, extended by zero
outside the certified time set. Source: Definition 3.40, p. 61, and
Claim 11.35, printed pp. 289-291. -/
noncomputable def normalizedCylinderScalar
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (x : C.carrier) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ I then F.scalar (e.pointMap s hs x) / scale else 0

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- Supplied M04 evolution and the actual affine cylinder clock give the
normalized derivative within the original time set, including endpoints.
Source: equation (3.7), p. 41, Definitions 3.38/3.40, p. 61, and
Claim 11.35, printed pp. 289-291. -/
theorem normalizedCylinderScalar_hasDerivWithinAt
    (hM04 : RicciFlowCurvatureTheory.{u})
    (e : GeneralizedFlowCylinder F C origin scale I U)
    {s : ℝ} (hs : s ∈ I) {x : C.carrier} (hx : x ∈ U) :
    let p := e.pointMap s hs x
    HasDerivWithinAt (normalizedCylinderScalar e x)
      (((F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 +
        2 * (F.connection p.1).ricciNormSq p.2) / scale ^ 2) I s := by
  obtain ⟨b, y, eta, heta, hcompat⟩ := e.vertical_compatibility s hs x hx
  let K := I ∩ Metric.ball s eta
  have hsK : s ∈ K := ⟨hs, Metric.mem_ball_self heta⟩
  obtain ⟨hb, hy⟩ := hcompat s hs (by simpa only [sub_self, abs_zero] using heta)
  have hmap : MapsTo (fun r : ℝ => origin + r / scale) K (F.box b).interval := by
    intro r hr
    obtain ⟨hrb, _⟩ := hcompat r hr.1
      (by simpa only [Metric.mem_ball, Real.dist_eq] using hr.2)
    exact hrb
  have hclock : HasDerivAt (fun r : ℝ => origin + r / scale) (1 / scale) s :=
    ((hasDerivAt_id s).div_const scale).const_add origin
  have hd := ((hM04.scalar_evolution 3 _ _ (F.box b).flow
    (origin + s / scale) hb y).comp s hclock.hasDerivWithinAt hmap).div_const scale
  have hsame : ∀ r ∈ K, normalizedCylinderScalar e x r =
      ((F.box b).flow.connection (origin + r / scale)).scalarCurvature y / scale := by
    intro r hr
    obtain ⟨hrb, hrxy⟩ := hcompat r hr.1
      (by simpa only [Metric.mem_ball, Real.dist_eq] using hr.2)
    simp only [normalizedCylinderScalar, dif_pos hr.1, GeneralizedRicciFlowData.scalar,
      GeneralizedFlowCylinder.pointMap, hrxy]
    rw [box_scalar_pullback F b (origin + r / scale) hrb y]
  have hdK := hd.congr_of_mem hsame hsK
  have hdI := (hasDerivWithinAt_inter (Metric.ball_mem_nhds s heta)).mp hdK
  apply hdI.congr_deriv
  rw [box_scalarEvolution_pullback F b (origin + s / scale) hb y, ← hy]
  dsimp only [GeneralizedFlowCylinder.pointMap]
  simp only [div_eq_mul_inv, one_mul]
  ring

/-- A pointwise actual small-Laplacian bound gives a positive quadratic
margin for the normalized scalar derivative. Source: equation (3.7),
p. 41, and Claim 11.35, printed pp. 289-291. -/
theorem normalizedCylinderScalar_derivative_ge_half_sq
    (hM04 : RicciFlowCurvatureTheory.{u})
    (e : GeneralizedFlowCylinder F C origin scale I U)
    {s : ℝ} (hs : s ∈ I) {x : C.carrier} (hx : x ∈ U)
    (hsmall : |(F.connection (origin + s / scale)).laplacian
        (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x)| ≤
      ((F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x)) ^ 2 / 6) :
    let p := e.pointMap s hs x
    let d := ((F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 +
      2 * (F.connection p.1).ricciNormSq p.2) / scale ^ 2
    HasDerivWithinAt (normalizedCylinderScalar e x) d I s ∧
      (normalizedCylinderScalar e x s) ^ 2 / 2 ≤ d := by
  refine ⟨normalizedCylinderScalar_hasDerivWithinAt hM04 e hs hx, ?_⟩
  have hsign := scalar_evolution_ge_half_sq_of_laplacian_bound
    (F.connection (origin + s / scale)) (e.forward s hs x) hsmall
  have hdiv := div_le_div_of_nonneg_right hsign (sq_nonneg scale)
  simpa only [normalizedCylinderScalar, dif_pos hs, GeneralizedRicciFlowData.scalar,
    GeneralizedFlowCylinder.pointMap, div_pow, div_right_comm] using hdiv

/-- One accuracy threshold supplies the actual signed worldline
derivative at every certified strong-neck center. Source: Definition
9.78, p. 232, equation (3.7), p. 41, and Claim 11.35, pp. 289-291. -/
theorem exists_strongNeck_normalizedCylinderScalar_derivative
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
        {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier},
        ∀ (e : GeneralizedFlowCylinder F C origin scale I U)
          {s : ℝ} (hs : s ∈ I) {x : C.carrier} (_hx : x ∈ U) {epsilon : ℝ}
          (N : GeneralizedStrongNeck F (origin + s / scale) epsilon),
          epsilon ≤ epsilon₀ → N.center = e.forward s hs x →
          let p := e.pointMap s hs x
          let d := ((F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 +
            2 * (F.connection p.1).ricciNormSq p.2) / scale ^ 2
          HasDerivWithinAt (normalizedCylinderScalar e x) d I s ∧
            (normalizedCylinderScalar e x s) ^ 2 / 2 ≤ d ∧ 0 < d := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ :=
    exists_strongNeck_center_scalarLaplacian_bound.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F C origin scale I U e s hs x hx epsilon N hepsilon hcenter
  have hbound := hcontrol N hepsilon
  rw [hcenter] at hbound
  have h := normalizedCylinderScalar_derivative_ge_half_sq hM04 e hs hx hbound
  have hR : 0 < (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) :=
    hcenter ▸ N.scalar_center_pos
  have hnormalized : 0 < normalizedCylinderScalar e x s := by
    simpa only [normalizedCylinderScalar, dif_pos hs, GeneralizedRicciFlowData.scalar,
      GeneralizedFlowCylinder.pointMap] using div_pos hR e.scale_pos
  exact ⟨h.1, h.2, lt_of_lt_of_le (div_pos (sq_pos_of_pos hnormalized) (by norm_num)) h.2⟩

end PoincareMT.M32
