import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Extension.FieldGaugeCover
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.JacobiGaugeCoordinates
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.RelativeCutoff

/-!
# Supported coordinates of an actual horizontal field

A real smooth weight supported in a compatible gauge neighborhood gives
coordinates smooth within the full closed time interval. Its actual
spatial tangent image is the weighted horizontal field. Morgan-Tian
Proposition 6.37 and Lemma 6.40, pp. 123-127.
-/

set_option autoImplicit false
-- Equal gauge basepoints retain the selected spacetime tangent model.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

private theorem horizontal_value_of_heq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} {w : G.Horizontal r} (hv : HEq v w) : v.val = w.val := by
  cases h
  exact congrArg Subtype.val (eq_of_heq hv)

/-- A supported scalar weight times the actual gauge coordinates
realizes the same weighted field and preserves its zero values,
Proposition 6.37 and Lemma 6.40, pp. 123-127. -/
theorem exists_weightedFieldGauge_coordinates (D : SquareFieldGaugePatch R)
    (Y : ∀ s, G.Horizontal (R.curve s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Y s))
        (M14SqrtParameterInterval a b))
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hsupport : tsupport ρ ⊆ D.parameterSet) :
    ∃ η : ℝ → EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ∞ η (M14SqrtParameterInterval a b) ∧
      tsupport η ⊆ D.parameterSet ∧
      (∀ s ∈ M14SqrtParameterInterval a b,
        ((G.gaugeCover.metric D.gauge).spatialTangentEquiv
          (D.lift (R.curve s)).1 (D.lift (R.curve s)).2 (η s)).val =
            ρ s • (Y s).val) ∧
      ∀ s ∈ M14SqrtParameterInterval a b, Y s = 0 → η s = 0 := by
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞
      (fun s => D.lift (R.curve s)) (M14SqrtParameterInterval a b ∩ D.parameterSet) :=
    D.lift_smooth.comp (R.smooth.mono (inter_subset_left.trans R.interval_subset)) D.curve_mem
  have hrec (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b ∩ D.parameterSet) :
      (G.gaugeCover.cylinder D.gauge).toSpacetime (D.lift (R.curve s)) = R.curve s :=
    D.right_inverse _ (D.curve_mem s hs)
  obtain ⟨f, hf, hfield⟩ := exists_smooth_horizontalGauge_coordinates D.gauge hβ hrec Y
    (hY.mono inter_subset_left)
  let η := fun s => ρ s • f s
  have hη : ContDiffOn ℝ ∞ η (M14SqrtParameterInterval a b) :=
    contDiffOn_smul_of_tsupport_subset D.parameter_open hρ hf hsupport
  have hηsupport : tsupport η ⊆ D.parameterSet :=
    (tsupport_smul_subset_left ρ f).trans hsupport
  have hvalue (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b) :
      ((G.gaugeCover.metric D.gauge).spatialTangentEquiv
        (D.lift (R.curve s)).1 (D.lift (R.curve s)).2 (η s)).val = ρ s • (Y s).val := by
    by_cases hz : ρ s = 0
    · simp only [η, hz, zero_smul, map_zero, Submodule.coe_zero]
    · have hs' := hsupport (subset_tsupport ρ (Function.mem_support.mpr hz))
      have hv := horizontal_value_of_heq (hrec s ⟨hs, hs'⟩).symm (hfield s ⟨hs, hs'⟩)
      simp only [η, map_smul, Submodule.coe_smul, ← hv]
  refine ⟨η, hη, hηsupport, hvalue, ?_⟩
  intro s hs hz
  have hv := hvalue s hs
  rw [hz, Submodule.coe_zero, smul_zero] at hv
  apply ((G.gaugeCover.metric D.gauge).spatialTangentEquiv
    (D.lift (R.curve s)).1 (D.lift (R.curve s)).2).injective
  rw [map_zero]
  exact Subtype.ext hv

end PoincareMT.M14
