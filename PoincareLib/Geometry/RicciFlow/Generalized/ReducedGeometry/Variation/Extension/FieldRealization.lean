import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Extension.ClosedAffineField
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.WeightedFieldCoordinates
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.FixedEndpointBoundary
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Actual variations realizing arbitrary smooth horizontal fields

A finite partition of unity and successive actual spatial perturbations
realize the entire prescribed field on the closed square interval.
Every zero of the field remains a fixed square point. Morgan-Tian
Proposition 6.37 and Lemma 6.40, pp. 123-127.
-/

set_option autoImplicit false
-- The actual horizontal bundle uses the retained spacetime tangent model.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

/-- The constant square family is an actual variation with zero
horizontal field, Proposition 6.37, pp. 123-127. -/
theorem exists_constant_squareVariation (R : M14SquareRootPath G p)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    ∃ V : M14LVariationData G p R,
      (∀ s ∈ M14SqrtParameterInterval a b, ∀ v, V.squareFamily s v = R.curve s) ∧
      ∀ s ∈ M14SqrtParameterInterval a b, M14VariationField V s = 0 := by
  have hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => R.curve z.1) (M14SqrtParameterInterval a b ×ˢ Ioo (-1) 1) :=
    (R.smooth.mono R.interval_subset).comp contMDiffOn_fst (fun _ hz => hz.1)
  obtain ⟨V, _, hV⟩ := exists_variationOfSquare_eqOn hM12 R (fun z => R.curve z.1)
    zero_lt_one hH (fun s hs _ _ => R.curve_time s hs) (fun _ _ => rfl)
  refine ⟨V, hV, fun s hs => variationField_eq_zero_of_constant V ?_⟩
  intro v _
  exact (hV s hs v).trans (hV s hs 0).symm

set_option maxHeartbeats 800000 in
-- Finite composition retains actual family, field and fixed-point witnesses together.
/-- Every smooth actual horizontal field on the closed square
interval is realized by an admissible variation, with every zero
retained as a fixed square point, Proposition 6.37 and Lemma 6.40,
pp. 123-127. -/
theorem exists_variation_of_smooth_horizontalField (R : M14SquareRootPath G p)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (Y : ∀ s, G.Horizontal (R.curve s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Y s))
        (M14SqrtParameterInterval a b)) :
    ∃ V : M14LVariationData G p R,
      (∀ s ∈ M14SqrtParameterInterval a b, M14VariationField V s = Y s) ∧
      ∀ s ∈ M14SqrtParameterInterval a b, Y s = 0 →
        ∀ v, V.squareFamily s v = R.curve s := by
  classical
  let C := M14SqrtParameterInterval a b
  obtain ⟨m, D, hcover⟩ := exists_finite_squareFieldGaugeCover R
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ))
    (show IsClosed C from isClosed_Icc) (fun i => (D i).parameterSet)
      (fun i => (D i).parameter_open) hcover
  choose η hη hηsupp hvalue hzero using fun i : Fin m =>
    exists_weightedFieldGauge_coordinates (D i) Y hY (ρ i) (ρ i).contMDiff.contDiff (hρ i)
  have hsrc (i : Fin m) (s : ℝ) (hs : s ∈ C ∩ tsupport (η i)) :
      R.curve s ∈ (D i).domain := (D i).curve_mem s ⟨hs.1, hηsupp i hs.2⟩
  have hfinite (L : Finset (Fin m)) :
      ∃ V : M14LVariationData G p R,
        (∀ s ∈ C, M14VariationField V s = ∑ i ∈ L, ρ i s • Y s) ∧
        ∀ s ∈ C, Y s = 0 → ∀ v, V.squareFamily s v = R.curve s := by
    induction L using Finset.induction_on with
    | empty =>
      obtain ⟨V, hV, hfield⟩ := exists_constant_squareVariation R hM12
      exact ⟨V, fun s hs => by simpa only [Finset.sum_empty] using hfield s hs,
        fun s hs _ => hV s hs⟩
    | @insert i L hi ih =>
      obtain ⟨V, hfield, hfixed⟩ := ih
      obtain ⟨W, _, hW⟩ := exists_supportedAffineGauge_variation_closed V (D i).gauge
        (D i).lift (η i) 1 hM12 (D i).domain_open (D i).lift_smooth
          (D i).right_inverse (hη i) (hsrc i)
      refine ⟨W, ?_, ?_⟩
      · intro s hs
        have hadd : M14VariationField W s = M14VariationField V s + ρ i s • Y s := by
          apply Subtype.ext
          rw [Submodule.coe_add, Submodule.coe_smul,
            variationField_supportedAffineGauge_val_closed V W (D i).gauge (D i).lift
              (η i) 1 hW (D i).domain_open (D i).lift_smooth (D i).right_inverse
                (hη i) (hsrc i) hs]
          dsimp only
          rw [one_smul, hvalue i s hs]
        rw [hadd, hfield s hs, Finset.sum_insert hi]
        exact add_comm _ _
      · intro s hs hz v
        rw [hW s hs v]
        exact supportedAffineGaugeFamily_fixed_of_zero V (D i).gauge (D i).lift (η i) 1
          (hzero i s hs hz) (hfixed s hs hz)
          (fun ht => (D i).right_inverse _ (hsrc i s ⟨hs, ht⟩)) v
  obtain ⟨V, hfield, hfixed⟩ := hfinite Finset.univ
  refine ⟨V, ?_, hfixed⟩
  intro s hs
  have hsum : ∑ i : Fin m, ρ i s = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hs
  rw [hfield s hs, ← Finset.sum_smul, hsum, one_smul]

/-- A fixed square-time point gives a fixed original-time point,
with the genuine square reparametrization, Lemma 6.40, pp. 123-124. -/
theorem variation_family_fixed_of_square {R : M14SquareRootPath G p}
    (V : M14LVariationData G p R) {t : ℝ} (ht : t ∈ Icc a b)
    (hfix : ∀ v, V.squareFamily (Real.sqrt t) v = R.curve (Real.sqrt t)) :
    ∀ v ∈ V.parameterDomain, V.family t v = p.curve t := by
  have hs : Real.sqrt t ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt ht.1, Real.sqrt_le_sqrt ht.2⟩
  intro v hv
  have heq := V.square_agrees _ hs v hv
  rw [Real.sq_sqrt (p.tau_nonneg.trans ht.1)] at heq
  rw [← heq, hfix v, R.agrees _ hs, Real.sq_sqrt (p.tau_nonneg.trans ht.1)]

/-- Every smooth field vanishing initially is realized by an
initial-fixed admissible variation. A zero terminal field also fixes
the terminal endpoint, Proposition 6.37, pp. 123-127. -/
theorem exists_initialFixed_variation_of_smooth_horizontalField
    (R : M14SquareRootPath G p) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (Y : ∀ s, G.Horizontal (R.curve s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Y s))
        (M14SqrtParameterInterval a b)) (hleft : Y (Real.sqrt a) = 0) :
    ∃ V : M14LVariationData G p R, V.left_endpoint_fixed ∧
      (∀ s ∈ M14SqrtParameterInterval a b, M14VariationField V s = Y s) ∧
      (Y (Real.sqrt b) = 0 → V.right_endpoint_fixed) := by
  obtain ⟨V, hfield, hfixed⟩ := exists_variation_of_smooth_horizontalField R hM12 Y hY
  have hab := Real.sqrt_le_sqrt p.tau_lt.le
  exact ⟨V, V.left_endpoint_fixed_spec.mpr
    (variation_family_fixed_of_square V ⟨le_rfl, p.tau_lt.le⟩
      (hfixed _ ⟨le_rfl, hab⟩ hleft)), hfield, fun hz => V.right_endpoint_fixed_spec.mpr
        (variation_family_fixed_of_square V ⟨p.tau_lt.le, le_rfl⟩
          (hfixed _ ⟨hab, le_rfl⟩ hz))⟩

end PoincareMT.M14
