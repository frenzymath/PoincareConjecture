import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.PLFiberCompression

/-!
# Scalar PL tents with exact closed core and support

A clipped affine function of absolute value equals one on
the prescribed inner interval and zero on the outer closed
exterior. It supplies actual periodic cutoffs in the stable
torus construction. See Hudson pp. 15--19 and M76 derivation
270, for Hamilton 1976, p. 66.
-/

set_option autoImplicit false

open Set Geometry

namespace PLScalarTent

/-- The actual clipped scalar tent. Its totalized denominator
is used geometrically only under the later strict radius
inequality. See M76 derivation 270. -/
noncomputable def value (r R s : ℝ) : ℝ :=
  min 1 (max 0 ((R - |s|) / (R - r)))

/-- Every scalar tent value lies in the unit interval, even
for totalized degenerate parameters. See M76 derivation 270. -/
theorem value_mem_unit (r R s : ℝ) : value r R s ∈ Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- The entire closed inner interval is fixed at one when
the outer radius is strictly larger. See derivation 270. -/
theorem value_eq_one {r R s : ℝ} (hrR : r < R) (hs : |s| ≤ r) :
    value r R s = 1 := by
  have h : 1 ≤ (R - |s|) / (R - r) :=
    (one_le_div (sub_pos.mpr hrR)).mpr (by linarith)
  exact min_eq_left (h.trans (le_max_right _ _))

/-- The whole closed outer exterior has literal zero value.
See M76 derivation 270. -/
theorem value_eq_zero {r R s : ℝ} (hrR : r < R) (hs : R ≤ |s|) :
    value r R s = 0 := by
  unfold value
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_pos.mpr hrR).le)]
  norm_num

/-- The fixed-parameter scalar tent is continuous on the
entire real line. See M76 derivation 270. -/
theorem continuous_value (r R : ℝ) : Continuous (value r R) := by
  unfold value
  fun_prop

/-- The tent has actual finite PL formulas on every finite
real carrier. The reciprocal denominator is a fixed scalar.
See Hudson pp. 15--19 and M76 derivation 270. -/
theorem finitePiecewiseAffineOn_value (r R : ℝ)
    (K : SimplicialComplex ℝ ℝ) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (value r R) K.space := by
  have hi := (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hK
  have hn := (K.affineOnFaces_affine (-ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hK
  have habs : FinitePiecewiseAffineOn (abs : ℝ → ℝ) K.space :=
    (hi.max hn).congr (fun _ _ => abs_eq_max_neg.symm)
  have hR := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ ℝ R)).finitePiecewiseAffineOn hK
  have hone := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ ℝ (1 : ℝ))).finitePiecewiseAffineOn hK
  have hdiv : FinitePiecewiseAffineOn (fun s => (R - |s|) / (R - r)) K.space := by
    apply ((hR.sub habs).postcomp ((R - r)⁻¹ • ContinuousAffineMap.id ℝ ℝ)).congr
    intro s _
    change (R - r)⁻¹ * (R - |s|) = (R - |s|) / (R - r)
    rw [div_eq_mul_inv, mul_comm]
  exact hone.min hdiv.positivePart

/-- The tent is locally PL everywhere, including all its
breakpoints. See M76 derivation 270. -/
theorem locallyPiecewiseAffineOn_value (r R : ℝ) :
    LocallyPiecewiseAffineOn (value r R) univ := by
  intro x _
  obtain ⟨K, hK, hxK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
  obtain ⟨J, hJ, hJK, hv⟩ := finitePiecewiseAffineOn_value r R K hK
  refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, hv⟩
  rw [hJK]
  exact hxK (mem_singleton x)

end PLScalarTent
