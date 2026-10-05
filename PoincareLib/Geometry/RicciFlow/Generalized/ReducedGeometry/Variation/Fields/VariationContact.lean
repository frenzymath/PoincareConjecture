import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Action.VariationAction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Fields.VariationPaths
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Fields.VariationClock
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareCurveEndpoints
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.LLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Families.ClosedFamilyPrimitive

/-!
# Actual variation actions and finite lower contacts

The smooth closed action integral supplies the parameter germ. Its
admissible moving-endpoint path bounds the actual action infimum only
on the finite-value domain. Morgan-Tian Lemma 6.22 and Lemma 6.40,
pp. 115-116, 126-127.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

/-- The actual variation action is smooth on its entire open parameter
domain, Lemma 6.22, pp. 115-116. -/
theorem variationAction_contDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) : ContDiffOn ℝ ∞ (M14VariationAction V) V.parameterDomain := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hi := closedFamilyPrimitive_contDiffOn hab hP (variationActionDensity V)
    (variationActionDensity_contDiffOn hM12 V)
  have hslice : ContDiffOn ℝ ∞
      (fun v => ∫ s in Real.sqrt a..Real.sqrt b, variationActionDensity V (s, v))
      V.parameterDomain :=
    hi.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hv => ⟨hv, hab.le, le_rfl⟩)
  exact hslice.congr (fun _ hv => variationAction_eq_squareIntegral V hv)

/-- Every actual closed-time endpoint curve is smooth in the open
variation parameter, Proposition 6.33, pp. 120-121. -/
theorem variationEndpoint_contMDiffOn (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (V.squareFamily s) V.parameterDomain :=
  V.square_smooth.comp ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn
    (fun _ hv => V.square_contains ⟨hs, hv⟩)

/-- An initial-fixed variation gives a genuine competitor with its
actual moving endpoint and exactly the variation action, Lemma 6.40,
pp. 126-127. -/
theorem exists_initialFixed_variationEndpointPath
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (V : M14LVariationData G p R)
    (hfix : V.left_endpoint_fixed) {v : ℝ} (hv : v ∈ V.parameterDomain) :
    ∃ q : M14BackwardPath G T a b x (V.squareFamily (Real.sqrt b) v),
      M14BackwardLAction G q = M14VariationAction V v := by
  let α := fun s => V.squareFamily s v
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b) :=
    V.square_smooth.comp (contMDiff_id.prodMk (contMDiff_const (c := v))).contMDiffOn
      (fun _ hs => V.square_contains ⟨hs, hv⟩)
  have hclock (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b) :
      G.spacetime.timeFunction (α s) = T - s ^ 2 := variation_squareFamily_time V hs hv
  have hleft : α (Real.sqrt a) = x := by
    rw [show α (Real.sqrt a) = V.family a v from by
      simpa only [Real.sq_sqrt p.tau_nonneg] using V.square_agrees (Real.sqrt a)
        ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩ v hv]
    exact ((V.left_endpoint_fixed_spec.mp hfix) v hv).trans p.curve_start
  refine ⟨backwardPathOfSquareCurveBetween hM12 p.tau_nonneg p.tau_lt α hα hclock hleft rfl, ?_⟩
  rw [← integral_squareCurveDensity_eq_action_between hM12 p.tau_nonneg p.tau_lt
    α hα Subset.rfl hclock hleft rfl, variationAction_eq_squareIntegral V hv]
  rfl

/-- On the actual finite-value domain, normalized variation action
is an upper bound for raw endpoint reduced length, Definition 6.45
and Lemma 6.40, pp. 129, 126-127. -/
theorem reducedLengthAt_le_variationAction
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (V : M14LVariationData G p R)
    (hfix : V.left_endpoint_fixed) {v : ℝ} (hv : v ∈ V.parameterDomain)
    (hfinite : M14FiniteValueDomain G T a b x (V.squareFamily (Real.sqrt b) v)) :
    M14ReducedLengthAt G T a x (V.squareFamily (Real.sqrt b) v) ≤
      M14VariationAction V v / (2 * Real.sqrt b) := by
  obtain ⟨q, hq⟩ := exists_initialFixed_variationEndpointPath hM12 V hfix hv
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  unfold M14ReducedLengthAt
  rw [variation_squareFamily_time V ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩ hv,
    Real.sq_sqrt hb.le, sub_sub_cancel]
  exact (div_le_div_of_nonneg_right (actionValue_le_action hfinite q)
    (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)).le).trans_eq (congrArg (· / (2 * Real.sqrt b)) hq)

/-- A smooth finite lower contact produces the actual scalar action
gap minimum used in the Hessian comparison, Lemma 6.40, pp. 126-127. -/
theorem isLocalMin_variationAction_gap
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (V : M14LVariationData G p R)
    (hfix : V.left_endpoint_fixed) (f : G.Point → ℝ)
    (hvalue : f (R.curve (Real.sqrt b)) = M14BackwardLAction G p / (2 * Real.sqrt b))
    (hcontact : ∀ᶠ q in 𝓝 (R.curve (Real.sqrt b)), f q ≤ M14ReducedLengthAt G T a x q)
    (hfinite : ∀ᶠ q in 𝓝 (R.curve (Real.sqrt b)),
      M14FiniteValueDomain G T a (T - G.spacetime.timeFunction q) x q) :
    IsLocalMin (fun v => M14VariationAction V v -
      (2 * Real.sqrt b) * f (V.squareFamily (Real.sqrt b) v)) 0 := by
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  have hc : 0 < 2 * Real.sqrt b := mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hη := ((variationEndpoint_contMDiffOn V hs).contMDiffAt (hP.mem_nhds hzero)).continuousAt
  have hnear : ∀ᶠ v in 𝓝 (0 : ℝ),
      f (V.squareFamily (Real.sqrt b) v) ≤
        M14ReducedLengthAt G T a x (V.squareFamily (Real.sqrt b) v) ∧
      M14FiniteValueDomain G T a
        (T - G.spacetime.timeFunction (V.squareFamily (Real.sqrt b) v)) x
        (V.squareFamily (Real.sqrt b) v) :=
    hη.tendsto.eventually (V.square_base (Real.sqrt b) ▸ hcontact.and hfinite)
  have hgap : M14VariationAction V 0 -
      (2 * Real.sqrt b) * f (V.squareFamily (Real.sqrt b) 0) = 0 := by
    rw [variationAction_zero, V.square_base, hvalue, mul_div_cancel₀ _ hc.ne', sub_self]
  filter_upwards [hP.mem_nhds hzero, hnear] with v hv hcontact'
  change M14VariationAction V 0 - (2 * Real.sqrt b) * f (V.squareFamily (Real.sqrt b) 0) ≤ _
  rw [hgap]
  have hfin := hcontact'.2
  rw [variation_squareFamily_time V hs hv, Real.sq_sqrt hb.le, sub_sub_cancel] at hfin
  exact sub_nonneg.mpr (by simpa only [mul_comm] using ((le_div_iff₀ hc).mp
    (hcontact'.1.trans (reducedLengthAt_le_variationAction hM12 V hfix hv hfin))))

end PoincareMT.M14
