import PoincareLib.Geometry.Manifold.RegularLevel.AdaptedChart
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Regular-level ChartedSpace

Adapted from LeeRiemannian, `LeeLib/Geometry/LevelSetChartedSpace.lean`.
See `references/geometry/lee-riemannian/` for provenance.
Lee, Introduction to Riemannian Manifolds, Corollary A.26 and Proposition 2.37.
-/

open Set Function
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Poincare.Geometry.Manifold.RegularLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ## The hyperplane of the differential -/

/-- The differential `df_y`, as a continuous linear functional on the model
space `E` (the tangent space is definitionally `E`). -/
def levelDifferential (f : M → ℝ) (y : M) : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f y

@[simp] theorem levelDifferential_apply (f : M → ℝ) (y : M) (u : E) :
    levelDifferential (I := I) f y u = mfderivReal (I := I) f y u := rfl

theorem levelDifferential_ne_zero {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    (levelDifferential (I := I) f y : E →ₗ[ℝ] ℝ) ≠ 0 := by
  intro h0
  exact hdf (ContinuousLinearMap.ext fun u => DFunLike.congr_fun h0 u)

/-- **The model hyperplane of the level set through `y`**: the kernel of the
differential, `ker df_y ⊆ E`.  In the adapted chart the level set reads as the
affine translate `κ y + ker df_y` of this hyperplane. -/
def levelHyperplane (f : M → ℝ) (y : M) : Submodule ℝ E :=
  LinearMap.ker (levelDifferential (I := I) f y : E →ₗ[ℝ] ℝ)

theorem mem_levelHyperplane_iff (f : M → ℝ) (y : M) (u : E) :
    u ∈ levelHyperplane (I := I) f y ↔ mfderivReal (I := I) f y u = 0 :=
  LinearMap.mem_ker

/-- A **transversal direction** at a regular point: a vector `e` with
`df_y e = 1`.  It spans a complement of `ker df_y`, and `levelProj` projects
onto the hyperplane along it. -/
def levelTransversal {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) : E :=
  have h : ∃ w : E, levelDifferential (I := I) f y w ≠ 0 := by
    by_contra h
    push Not at h
    exact hdf (ContinuousLinearMap.ext fun v => by simpa using h v)
  (levelDifferential (I := I) f y h.choose)⁻¹ • h.choose

@[simp] theorem levelDifferential_levelTransversal {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    levelDifferential (I := I) f y (levelTransversal (I := I) hdf) = 1 := by
  have h : ∃ w : E, levelDifferential (I := I) f y w ≠ 0 := by
    by_contra h
    push Not at h
    exact hdf (ContinuousLinearMap.ext fun v => by simpa using h v)
  rw [levelTransversal, map_smul, smul_eq_mul, inv_mul_cancel₀ h.choose_spec]

/-- **The projection onto the hyperplane along the transversal**:
`u ↦ u - df_y u • e`.  This is the splitting `E = ker df_y ⊕ ℝ ∙ e` made
explicit; it uses no orthogonality, hence no inner product on `E`. -/
def levelProj {f : M → ℝ} {y : M} (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    E →L[ℝ] levelHyperplane (I := I) f y :=
  ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.id ℝ E -
      (levelDifferential (I := I) f y).smulRight (levelTransversal (I := I) hdf))
    (levelHyperplane (I := I) f y)
    (fun u => by
      simp only [mem_levelHyperplane_iff, ← levelDifferential_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, map_sub, map_smul, smul_eq_mul,
        levelDifferential_levelTransversal hdf, mul_one, sub_self])

@[simp] theorem levelProj_coe {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) (u : E) :
    (levelProj (I := I) hdf u : E)
      = u - levelDifferential (I := I) f y u • levelTransversal (I := I) hdf :=
  rfl

theorem levelProj_of_mem {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) {u : E}
    (hu : u ∈ levelHyperplane (I := I) f y) :
    (levelProj (I := I) hdf u : E) = u := by
  have h : levelDifferential (I := I) f y u = 0 :=
    (mem_levelHyperplane_iff (I := I) f y u).1 hu
  rw [levelProj_coe, h, zero_smul, sub_zero]

section Dimension

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

/-- The hyperplane `ker df_y` has dimension `n`: the differential is a nonzero
functional on the `(n+1)`-dimensional model space. -/
theorem finrank_levelHyperplane {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    Module.finrank ℝ (levelHyperplane (I := I) f y) = n := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (levelDifferential_ne_zero (I := I) hdf)
  rw [Fact.out (p := Module.finrank ℝ E = n + 1)] at h
  show Module.finrank ℝ
    (LinearMap.ker (levelDifferential (I := I) f y : E →ₗ[ℝ] ℝ)) = n
  omega

/-- **The identification of the hyperplane with the fixed model space**: any
two real vector spaces of the same finite dimension are continuously linearly
equivalent, and `ker df_y` and `EuclideanSpace ℝ (Fin n)` both have dimension
`n`.  This is what lets slice charts at *different* points of the level set
share one model space, which a `ChartedSpace` requires.

Poincare's analogous step uses an orthonormal basis of `(ℝ ∙ w_y)ᗮ`, which
forces an inner product on the model; here no structure beyond finite
dimensionality is used. -/
def levelHyperplaneEquiv {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    levelHyperplane (I := I) f y ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_levelHyperplane n hdf, finrank_euclideanSpace_fin])

/-- The ambient **slice projection** `E → EuclideanSpace ℝ (Fin n)`: project to
the hyperplane along the transversal, then take coordinates. -/
def sliceProj {f : M → ℝ} {y : M} (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (levelHyperplaneEquiv (I := I) n hdf : levelHyperplane (I := I) f y →L[ℝ] _)
    ∘L levelProj (I := I) hdf

/-- The ambient **slice embedding** `EuclideanSpace ℝ (Fin n) → E`: coordinates
back into the hyperplane, included into `E`. -/
def sliceEmb {f : M → ℝ} {y : M} (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] E :=
  (levelHyperplane (I := I) f y).subtypeL
    ∘L ((levelHyperplaneEquiv (I := I) n hdf).symm :
      EuclideanSpace ℝ (Fin n) →L[ℝ] levelHyperplane (I := I) f y)

theorem sliceEmb_mem {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) (z : EuclideanSpace ℝ (Fin n)) :
    sliceEmb (I := I) n hdf z ∈ levelHyperplane (I := I) f y :=
  ((levelHyperplaneEquiv (I := I) n hdf).symm z).2

@[simp] theorem sliceProj_sliceEmb {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) (z : EuclideanSpace ℝ (Fin n)) :
    sliceProj (I := I) n hdf (sliceEmb (I := I) n hdf z) = z := by
  have hmem : sliceEmb (I := I) n hdf z ∈ levelHyperplane (I := I) f y :=
    sliceEmb_mem (I := I) n hdf z
  have hproj : levelProj (I := I) hdf (sliceEmb (I := I) n hdf z)
      = ((levelHyperplaneEquiv (I := I) n hdf).symm z) :=
    Subtype.ext (levelProj_of_mem (I := I) hdf hmem)
  simp only [sliceProj, ContinuousLinearMap.coe_comp', Function.comp_apply,
    hproj, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The slice embedding is injective: it is a linear equivalence onto the
hyperplane followed by the inclusion of a submodule. -/
theorem sliceEmb_injective {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    Function.Injective ⇑(sliceEmb (I := I) n hdf) := by
  intro u v huv
  simp only [sliceEmb, ContinuousLinearMap.coe_comp', Function.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe] at huv
  exact (ContinuousLinearEquiv.injective _) (Subtype.coe_injective huv)

theorem sliceEmb_sliceProj_of_mem {f : M → ℝ} {y : M}
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) {u : E}
    (hu : u ∈ levelHyperplane (I := I) f y) :
    sliceEmb (I := I) n hdf (sliceProj (I := I) n hdf u) = u := by
  have hproj : levelProj (I := I) hdf u = (⟨u, hu⟩ : levelHyperplane (I := I) f y) :=
    Subtype.ext (levelProj_of_mem (I := I) hdf hu)
  simp only [sliceProj, sliceEmb, ContinuousLinearMap.coe_comp',
    Function.comp_apply, hproj, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, Submodule.subtypeL_apply]

end Dimension

/-! ## The adapted straightening chart, extracted -/

section AdaptedChart

variable {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M)
  (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0)

/-- A choice of straightening correction `G` for the extended chart at `y`
(`exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine`): in the
corrected chart `G ∘ extChartAt I y`, the function `f` is affine. -/
def adaptedStraightening : OpenPartialHomeomorph E E :=
  (exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine hf y hdf).choose

theorem adaptedStraightening_source_subset :
    (adaptedStraightening hf y hdf).source ⊆ (extChartAt I y).target :=
  (exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    hf y hdf).choose_spec.1

theorem mem_adaptedStraightening_source :
    extChartAt I y y ∈ (adaptedStraightening hf y hdf).source :=
  (exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    hf y hdf).choose_spec.2.1

theorem adaptedStraightening_center :
    adaptedStraightening hf y hdf (extChartAt I y y) = extChartAt I y y :=
  (exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    hf y hdf).choose_spec.2.2.1

theorem extChartAt_self_mem_adaptedStraightening_target :
    extChartAt I y y ∈ (adaptedStraightening hf y hdf).target := by
  have h := (adaptedStraightening hf y hdf).map_source
    (mem_adaptedStraightening_source hf y hdf)
  rwa [adaptedStraightening_center hf y hdf] at h

theorem adaptedStraightening_symm_center :
    (adaptedStraightening hf y hdf).symm (extChartAt I y y)
      = extChartAt I y y := by
  conv_lhs => rw [← adaptedStraightening_center hf y hdf]
  exact (adaptedStraightening hf y hdf).left_inv
    (mem_adaptedStraightening_source hf y hdf)

theorem contDiffOn_adaptedStraightening :
    ContDiffOn ℝ ∞ (adaptedStraightening hf y hdf)
      (adaptedStraightening hf y hdf).source :=
  (exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    hf y hdf).choose_spec.2.2.2.1

theorem contDiffOn_adaptedStraightening_symm :
    ContDiffOn ℝ ∞ (adaptedStraightening hf y hdf).symm
      (adaptedStraightening hf y hdf).target :=
  (exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    hf y hdf).choose_spec.2.2.2.2.1

theorem comp_adaptedStraightening_symm_eq_affine :
    ∀ v ∈ (adaptedStraightening hf y hdf).target,
      f ((extChartAt I y).symm ((adaptedStraightening hf y hdf).symm v))
        = f y + mfderivReal (I := I) f y (v - extChartAt I y y) :=
  (exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    hf y hdf).choose_spec.2.2.2.2.2

/-- The straightening has invertible differential at the chart centre:
`dG_{κ y} ∘ d(G⁻¹)_{κ y} = id`, because `G ∘ G⁻¹ = id` near `κ y`.  In
particular `d(G⁻¹)_{κ y}` is injective — this is what makes the level set
inclusion an immersion. -/
theorem fderiv_adaptedStraightening_comp_fderiv_symm :
    (fderiv ℝ (adaptedStraightening hf y hdf) (extChartAt I y y)) ∘L
      (fderiv ℝ (adaptedStraightening hf y hdf).symm (extChartAt I y y))
      = ContinuousLinearMap.id ℝ E := by
  have hmemT := extChartAt_self_mem_adaptedStraightening_target hf y hdf
  have hmemS := mem_adaptedStraightening_source hf y hdf
  have hsymm : HasFDerivAt (adaptedStraightening hf y hdf).symm
      (fderiv ℝ (adaptedStraightening hf y hdf).symm (extChartAt I y y))
      (extChartAt I y y) :=
    (((contDiffOn_adaptedStraightening_symm hf y hdf).contDiffAt
      ((adaptedStraightening hf y hdf).open_target.mem_nhds
        hmemT)).differentiableAt (by simp)).hasFDerivAt
  have hG : HasFDerivAt (adaptedStraightening hf y hdf)
      (fderiv ℝ (adaptedStraightening hf y hdf) (extChartAt I y y))
      ((adaptedStraightening hf y hdf).symm (extChartAt I y y)) := by
    rw [adaptedStraightening_symm_center hf y hdf]
    exact (((contDiffOn_adaptedStraightening hf y hdf).contDiffAt
      ((adaptedStraightening hf y hdf).open_source.mem_nhds
        hmemS)).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hG.comp (extChartAt I y y) hsymm
  have hev : (id : E → E) =ᶠ[𝓝 (extChartAt I y y)]
      (⇑(adaptedStraightening hf y hdf)
        ∘ ⇑(adaptedStraightening hf y hdf).symm) :=
    (Filter.eventually_of_mem
      ((adaptedStraightening hf y hdf).open_target.mem_nhds hmemT)
      fun v hv => ((adaptedStraightening hf y hdf).right_inv hv).symm)
  exact (hcomp.congr_of_eventuallyEq hev).unique (hasFDerivAt_id _)

theorem fderiv_adaptedStraightening_symm_injective :
    Function.Injective
      ⇑(fderiv ℝ (adaptedStraightening hf y hdf).symm (extChartAt I y y)) := by
  intro u v huv
  have h := congrArg
    (⇑(fderiv ℝ (adaptedStraightening hf y hdf) (extChartAt I y y))) huv
  have hid := fderiv_adaptedStraightening_comp_fderiv_symm hf y hdf
  have hu := ContinuousLinearMap.ext_iff.1 hid u
  have hv := ContinuousLinearMap.ext_iff.1 hid v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq] at hu hv
  rw [← hu, ← hv]
  exact h

/-- On the level set through `y`, the straightened coordinate lies in the
hyperplane: for `x` on the level set and in the chart domain,
`G (κ x) - κ y ∈ ker df_y`.  This is the slice normal form of the level set. -/
theorem adaptedStraightening_sub_mem_levelHyperplane {x : M} (hx : f x = f y)
    (hx1 : x ∈ (extChartAt I y).source)
    (hx2 : extChartAt I y x ∈ (adaptedStraightening hf y hdf).source) :
    adaptedStraightening hf y hdf (extChartAt I y x) - extChartAt I y y
      ∈ levelHyperplane (I := I) f y := by
  rw [mem_levelHyperplane_iff]
  have hv : adaptedStraightening hf y hdf (extChartAt I y x)
      ∈ (adaptedStraightening hf y hdf).target :=
    (adaptedStraightening hf y hdf).map_source hx2
  have h := comp_adaptedStraightening_symm_eq_affine hf y hdf _ hv
  rw [(adaptedStraightening hf y hdf).left_inv hx2,
    (extChartAt I y).left_inv hx1, hx] at h
  linarith

end AdaptedChart

/-! ## The slice chart on a level set -/

section SliceChart

variable {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M)
  (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0)

/-- The domain in `M` of the slice chart at `y`: the locus where the corrected
chart `G ∘ κ` is defined. -/
def levelChartDomain : Set M :=
  (extChartAt I y).source
    ∩ extChartAt I y ⁻¹' (adaptedStraightening hf y hdf).source

theorem isOpen_levelChartDomain : IsOpen (levelChartDomain hf y hdf) :=
  isOpen_extChartAt_preimage' y (adaptedStraightening hf y hdf).open_source

theorem mem_levelChartDomain_self : y ∈ levelChartDomain hf y hdf :=
  ⟨mem_extChartAt_source (I := I) y, mem_adaptedStraightening_source hf y hdf⟩

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

/-- The target in `EuclideanSpace ℝ (Fin n)` of the slice chart at `y`: those
hyperplane coordinates whose affine representative `κ y + ι z` lies in the
target of the straightening. -/
def levelSliceTarget : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun z => extChartAt I y y + sliceEmb (I := I) n hdf z)
    ⁻¹' (adaptedStraightening hf y hdf).target

theorem isOpen_levelSliceTarget : IsOpen (levelSliceTarget hf y hdf n) :=
  (adaptedStraightening hf y hdf).open_target.preimage
    (continuous_const.add (sliceEmb (I := I) n hdf).continuous)

theorem mfderivReal_sliceEmb (z : EuclideanSpace ℝ (Fin n)) :
    mfderivReal (I := I) f y (sliceEmb (I := I) n hdf z) = 0 :=
  (mem_levelHyperplane_iff (I := I) f y _).1 (sliceEmb_mem (I := I) n hdf z)

variable (c : ℝ)

/-- The inverse slice-chart point lies on the level set: reading the affine
representative back through the corrected chart lands in `f ⁻¹' {c}`, because
`f` is affine in the corrected chart and the hyperplane directions do not
change `f`. -/
theorem levelSliceInv_mem {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ levelSliceTarget hf y hdf n) (hy : f y = c) :
    (extChartAt I y).symm ((adaptedStraightening hf y hdf).symm
      (extChartAt I y y + sliceEmb (I := I) n hdf z)) ∈ (f ⁻¹' {c} : Set M) := by
  have h := comp_adaptedStraightening_symm_eq_affine hf y hdf _ hz
  rw [mem_preimage, mem_singleton_iff, h, add_sub_cancel_left,
    mfderivReal_sliceEmb, add_zero, hy]

/-- The inverse slice-chart point lies in the chart domain. -/
theorem levelSliceInv_mem_domain {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ levelSliceTarget hf y hdf n) :
    (extChartAt I y).symm ((adaptedStraightening hf y hdf).symm
      (extChartAt I y y + sliceEmb (I := I) n hdf z))
      ∈ levelChartDomain hf y hdf := by
  have h1 : (adaptedStraightening hf y hdf).symm
      (extChartAt I y y + sliceEmb (I := I) n hdf z)
      ∈ (adaptedStraightening hf y hdf).source :=
    (adaptedStraightening hf y hdf).map_target hz
  have h2 := adaptedStraightening_source_subset hf y hdf h1
  refine ⟨(extChartAt I y).map_target h2, ?_⟩
  rw [mem_preimage, (extChartAt I y).right_inv h2]
  exact h1

/-- The slice round-trip: on level-set points of the chart domain, embedding
back the projected hyperplane coordinate recovers the corrected chart image —
the level set reads as the affine slice. -/
theorem levelSlice_emb_proj {x : M} (hxc : f x = f y)
    (hx : x ∈ levelChartDomain hf y hdf) :
    extChartAt I y y + sliceEmb (I := I) n hdf (sliceProj (I := I) n hdf
      (adaptedStraightening hf y hdf (extChartAt I y x) - extChartAt I y y))
      = adaptedStraightening hf y hdf (extChartAt I y x) := by
  rw [sliceEmb_sliceProj_of_mem (I := I) n hdf
    (adaptedStraightening_sub_mem_levelHyperplane hf y hdf hxc hx.1 hx.2)]
  abel

/-- Points of the level set satisfy `f x = c`. -/
theorem levelSet_prop (x : (f ⁻¹' {c} : Set M)) : f ↑x = c := x.2

open scoped Classical in
/-- **The slice chart of the level set at `y`**: the corrected chart `G ∘ κ` of
`M` (in which `f` is affine), recentred at `κ y` and read through the
hyperplane coordinates `ker df_y ≃ EuclideanSpace ℝ (Fin n)`.  Under this chart
the level set `f ⁻¹' {c}` corresponds to an open set of the model; these charts
form the atlas of the hypersurface structure (`levelSetChartedSpace`). -/
def levelSliceChart (hy : f y = c) :
    OpenPartialHomeomorph (f ⁻¹' {c} : Set M) (EuclideanSpace ℝ (Fin n)) where
  toFun x := sliceProj (I := I) n hdf
    (adaptedStraightening hf y hdf (extChartAt I y ↑x) - extChartAt I y y)
  invFun z :=
    if hz : z ∈ levelSliceTarget hf y hdf n then
      ⟨(extChartAt I y).symm ((adaptedStraightening hf y hdf).symm
        (extChartAt I y y + sliceEmb (I := I) n hdf z)),
        levelSliceInv_mem hf y hdf n c hz hy⟩
    else ⟨y, by simp [hy]⟩
  source := Subtype.val ⁻¹' levelChartDomain hf y hdf
  target := levelSliceTarget hf y hdf n
  map_source' x hx := by
    rw [mem_preimage] at hx
    have hxc : f ↑x = f y := by rw [levelSet_prop c x, hy]
    show extChartAt I y y + sliceEmb (I := I) n hdf _
      ∈ (adaptedStraightening hf y hdf).target
    rw [levelSlice_emb_proj hf y hdf n hxc hx]
    exact (adaptedStraightening hf y hdf).map_source hx.2
  map_target' z hz := by
    rw [mem_preimage, dif_pos hz]
    exact levelSliceInv_mem_domain hf y hdf n hz
  left_inv' x hx := by
    rw [mem_preimage] at hx
    have hxc : f ↑x = f y := by rw [levelSet_prop c x, hy]
    have hmem : sliceProj (I := I) n hdf
        (adaptedStraightening hf y hdf (extChartAt I y ↑x) - extChartAt I y y)
        ∈ levelSliceTarget hf y hdf n := by
      show extChartAt I y y + sliceEmb (I := I) n hdf _
        ∈ (adaptedStraightening hf y hdf).target
      rw [levelSlice_emb_proj hf y hdf n hxc hx]
      exact (adaptedStraightening hf y hdf).map_source hx.2
    rw [dif_pos hmem]
    refine Subtype.ext ?_
    show (extChartAt I y).symm ((adaptedStraightening hf y hdf).symm _) = ↑x
    rw [levelSlice_emb_proj hf y hdf n hxc hx,
      (adaptedStraightening hf y hdf).left_inv hx.2,
      (extChartAt I y).left_inv hx.1]
  right_inv' z hz := by
    rw [dif_pos hz]
    have h1 : (adaptedStraightening hf y hdf).symm
        (extChartAt I y y + sliceEmb (I := I) n hdf z)
        ∈ (adaptedStraightening hf y hdf).source :=
      (adaptedStraightening hf y hdf).map_target hz
    have h2 := adaptedStraightening_source_subset hf y hdf h1
    show sliceProj (I := I) n hdf
      (adaptedStraightening hf y hdf (extChartAt I y ((extChartAt I y).symm
        ((adaptedStraightening hf y hdf).symm
          (extChartAt I y y + sliceEmb (I := I) n hdf z)))) - extChartAt I y y) = z
    rw [(extChartAt I y).right_inv h2,
      (adaptedStraightening hf y hdf).right_inv hz, add_sub_cancel_left,
      sliceProj_sliceEmb]
  open_source :=
    (isOpen_levelChartDomain hf y hdf).preimage continuous_subtype_val
  open_target := isOpen_levelSliceTarget hf y hdf n
  continuousOn_toFun := by
    have h1 : ContinuousOn
        (fun x : M => adaptedStraightening hf y hdf (extChartAt I y x))
        (levelChartDomain hf y hdf) :=
      (adaptedStraightening hf y hdf).continuousOn.comp
        ((continuousOn_extChartAt (I := I) y).mono inter_subset_left)
        fun x hx => hx.2
    have h2 : ContinuousOn
        (fun x : (f ⁻¹' {c} : Set M) =>
          adaptedStraightening hf y hdf (extChartAt I y ↑x))
        (Subtype.val ⁻¹' levelChartDomain hf y hdf) :=
      h1.comp continuous_subtype_val.continuousOn fun x hx => hx
    exact ((sliceProj (I := I) n hdf).continuous.comp
      (continuous_id.sub continuous_const)).comp_continuousOn h2
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hg : ContinuousOn (fun z => (extChartAt I y).symm
        ((adaptedStraightening hf y hdf).symm
          (extChartAt I y y + sliceEmb (I := I) n hdf z)))
        (levelSliceTarget hf y hdf n) := by
      refine (continuousOn_extChartAt_symm (I := I) y).comp
        ((adaptedStraightening hf y hdf).continuousOn_symm.comp
          (continuous_const.add (sliceEmb (I := I) n hdf).continuous).continuousOn
          fun z hz => hz) ?_
      exact fun z hz => adaptedStraightening_source_subset hf y hdf
        ((adaptedStraightening hf y hdf).map_target hz)
    have hr : Continuous fun z : (levelSliceTarget hf y hdf n) =>
        (⟨(extChartAt I y).symm ((adaptedStraightening hf y hdf).symm
          (extChartAt I y y + sliceEmb (I := I) n hdf ↑z)),
          levelSliceInv_mem hf y hdf n c z.2 hy⟩ : (f ⁻¹' {c} : Set M)) :=
      (continuousOn_iff_continuous_restrict.1 hg).subtype_mk _
    convert hr using 1
    funext z
    simp only [restrict_apply, dif_pos z.2]

theorem levelSliceChart_source (hy : f y = c) :
    (levelSliceChart hf y hdf n c hy).source
      = Subtype.val ⁻¹' levelChartDomain hf y hdf := rfl

theorem levelSliceChart_target (hy : f y = c) :
    (levelSliceChart hf y hdf n c hy).target = levelSliceTarget hf y hdf n :=
  rfl

theorem levelSliceChart_apply (hy : f y = c) (x : (f ⁻¹' {c} : Set M)) :
    levelSliceChart hf y hdf n c hy x
      = sliceProj (I := I) n hdf
          (adaptedStraightening hf y hdf (extChartAt I y ↑x)
            - extChartAt I y y) := rfl

open scoped Classical in
theorem levelSliceChart_symm_apply (hy : f y = c)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ levelSliceTarget hf y hdf n) :
    ((levelSliceChart hf y hdf n c hy).symm z : M)
      = (extChartAt I y).symm ((adaptedStraightening hf y hdf).symm
          (extChartAt I y y + sliceEmb (I := I) n hdf z)) := by
  show (dite (z ∈ levelSliceTarget hf y hdf n) _ _ : (f ⁻¹' {c} : Set M)).val
    = _
  rw [dif_pos hz]

end SliceChart

/-! ## The charted-space and manifold structure -/

section ChartedSpaceLevelSet

variable {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] (c : ℝ)

/-- **The level set of a regular value as a charted space**: if `df_x ≠ 0` at
every point of `f ⁻¹' {c}`, the slice charts at the points of the level set
form an atlas modelled on `EuclideanSpace ℝ (Fin n)` — the level set is a
topological `n`-manifold. -/
@[reducible] def levelSetChartedSpace
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (f ⁻¹' {c} : Set M) where
  atlas := ⋃ x : (f ⁻¹' {c} : Set M),
    {levelSliceChart hf ↑x (hreg ↑x (levelSet_prop c x)) n c
      (levelSet_prop c x)}
  chartAt x := levelSliceChart hf ↑x (hreg ↑x (levelSet_prop c x)) n c
    (levelSet_prop c x)
  mem_chart_source x :=
    mem_levelChartDomain_self hf ↑x (hreg ↑x (levelSet_prop c x))
  chart_mem_atlas x := mem_iUnion.2 ⟨x, rfl⟩

/-- **Smoothness of the slice-chart transition maps**: the transition between
the slice charts at `y` and `y'` is, on its open domain, the composite of the
affine hyperplane parametrization, the inverse straightening at `y`, the
coordinate change of `M`, the straightening at `y'`, and the hyperplane
projection — all smooth maps of the model spaces.  This is the `C^∞`-pregroupoid
compatibility of the atlas. -/
theorem contDiffOn_levelSliceChart_trans (y y' : M)
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) (hdf' : mfderiv I 𝓘(ℝ, ℝ) f y' ≠ 0)
    (hy : f y = c) (hy' : f y' = c) :
    ContDiffOn ℝ ∞
      (((levelSliceChart hf y hdf n c hy).symm.trans
        (levelSliceChart hf y' hdf' n c hy')) :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      ((levelSliceChart hf y hdf n c hy).symm.trans
        (levelSliceChart hf y' hdf' n c hy')).source := by
  intro z hz
  have hz1 : z ∈ levelSliceTarget hf y hdf n := hz.1
  have hsymm := levelSliceChart_symm_apply hf y hdf n c hy hz1
  have hz2 : ((levelSliceChart hf y hdf n c hy).symm z : M)
      ∈ levelChartDomain hf y' hdf' := hz.2
  rw [hsymm] at hz2
  -- the five smooth pieces of the ambient transition composite
  have ha : ContDiffAt ℝ ∞
      (fun w : EuclideanSpace ℝ (Fin n) =>
        extChartAt I y y + sliceEmb (I := I) n hdf w) z :=
    (contDiff_const.add (sliceEmb (I := I) n hdf).contDiff).contDiffAt
  have hb : ContDiffAt ℝ ∞ (adaptedStraightening hf y hdf).symm
      (extChartAt I y y + sliceEmb (I := I) n hdf z) :=
    (contDiffOn_adaptedStraightening_symm hf y hdf).contDiffAt
      ((adaptedStraightening hf y hdf).open_target.mem_nhds hz1)
  have hsrc : ((extChartAt I y).symm ≫ extChartAt I y').source
      = (extChartAt I y).target
        ∩ (extChartAt I y).symm ⁻¹' (extChartAt I y').source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  have hcmem : (adaptedStraightening hf y hdf).symm
      (extChartAt I y y + sliceEmb (I := I) n hdf z)
      ∈ ((extChartAt I y).symm ≫ extChartAt I y').source := by
    rw [hsrc]
    exact ⟨adaptedStraightening_source_subset hf y hdf
      ((adaptedStraightening hf y hdf).map_target hz1), hz2.1⟩
  have hcopen : IsOpen (((extChartAt I y).symm ≫ extChartAt I y').source) := by
    rw [hsrc]
    exact (continuousOn_extChartAt_symm (I := I) y).isOpen_inter_preimage
      (isOpen_extChartAt_target y) (isOpen_extChartAt_source y')
  have hc : ContDiffAt ℝ ∞ (extChartAt I y' ∘ (extChartAt I y).symm)
      ((adaptedStraightening hf y hdf).symm
        (extChartAt I y y + sliceEmb (I := I) n hdf z)) :=
    (contDiffOn_ext_coord_change y' y).contDiffAt (hcopen.mem_nhds hcmem)
  have hd : ContDiffAt ℝ ∞ (adaptedStraightening hf y' hdf')
      (extChartAt I y' ((extChartAt I y).symm
        ((adaptedStraightening hf y hdf).symm
          (extChartAt I y y + sliceEmb (I := I) n hdf z)))) :=
    (contDiffOn_adaptedStraightening hf y' hdf').contDiffAt
      ((adaptedStraightening hf y' hdf').open_source.mem_nhds hz2.2)
  have he : ContDiffAt ℝ ∞
      (fun u : E => sliceProj (I := I) n hdf' (u - extChartAt I y' y'))
      (adaptedStraightening hf y' hdf'
        (extChartAt I y' ((extChartAt I y).symm
          ((adaptedStraightening hf y hdf).symm
            (extChartAt I y y + sliceEmb (I := I) n hdf z))))) :=
    ((sliceProj (I := I) n hdf').contDiff.comp
      (contDiff_id.sub contDiff_const)).contDiffAt
  have h1 : ContDiffAt ℝ ∞
      ((extChartAt I y' ∘ (extChartAt I y).symm)
        ∘ (adaptedStraightening hf y hdf).symm)
      (extChartAt I y y + sliceEmb (I := I) n hdf z) :=
    hc.comp _ hb
  have h2 : ContDiffAt ℝ ∞
      (((extChartAt I y' ∘ (extChartAt I y).symm)
          ∘ (adaptedStraightening hf y hdf).symm)
        ∘ fun w : EuclideanSpace ℝ (Fin n) =>
          extChartAt I y y + sliceEmb (I := I) n hdf w) z :=
    h1.comp z ha
  have h3 : ContDiffAt ℝ ∞
      ((adaptedStraightening hf y' hdf')
        ∘ (((extChartAt I y' ∘ (extChartAt I y).symm)
            ∘ (adaptedStraightening hf y hdf).symm)
          ∘ fun w : EuclideanSpace ℝ (Fin n) =>
            extChartAt I y y + sliceEmb (I := I) n hdf w)) z :=
    hd.comp z h2
  have hcomp : ContDiffAt ℝ ∞
      ((fun u : E => sliceProj (I := I) n hdf' (u - extChartAt I y' y'))
        ∘ ((adaptedStraightening hf y' hdf')
          ∘ (((extChartAt I y' ∘ (extChartAt I y).symm)
              ∘ (adaptedStraightening hf y hdf).symm)
            ∘ fun w : EuclideanSpace ℝ (Fin n) =>
              extChartAt I y y + sliceEmb (I := I) n hdf w))) z :=
    he.comp z h3
  refine hcomp.contDiffWithinAt.congr ?_ ?_
  · intro w hw
    have hw1 : w ∈ levelSliceTarget hf y hdf n := hw.1
    rw [OpenPartialHomeomorph.trans_apply,
      levelSliceChart_apply hf y' hdf' n c hy',
      levelSliceChart_symm_apply hf y hdf n c hy hw1]
    rfl
  · rw [OpenPartialHomeomorph.trans_apply,
      levelSliceChart_apply hf y' hdf' n c hy',
      levelSliceChart_symm_apply hf y hdf n c hy hz1]
    rfl

/-- **A regular level set is a smooth hypersurface** — the codimension-one case
of Lee's Corollary A.26, and the first half of his Proposition 2.37.

With the slice-chart atlas, `f ⁻¹' {c}` is a `C^∞` manifold modelled on
`EuclideanSpace ℝ (Fin n)`.  The transition maps are smooth because in the
corrected charts the level set reads as an affine hyperplane slice. -/
theorem isManifold_levelSet
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := levelSetChartedSpace hf n c hreg
    IsManifold (𝓡 n) ∞ (f ⁻¹' {c} : Set M) := by
  letI := levelSetChartedSpace hf n c hreg
  refine isManifold_of_contDiffOn (𝓡 n) ∞ (f ⁻¹' {c} : Set M) ?_
  intro e e' he he'
  obtain ⟨x, hx⟩ := mem_iUnion.1 he
  obtain ⟨x', hx'⟩ := mem_iUnion.1 he'
  rw [mem_singleton_iff] at hx hx'
  subst hx hx'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.inter_univ, Set.preimage_id, Function.comp_def, id_eq]
  exact contDiffOn_levelSliceChart_trans hf n c ↑x ↑x' _ _ _ _

theorem levelSetChartedSpace_chartAt
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : (f ⁻¹' {c} : Set M)) :
    (letI := levelSetChartedSpace hf n c hreg;
      chartAt (EuclideanSpace ℝ (Fin n)) x)
      = levelSliceChart hf ↑x (hreg ↑x (levelSet_prop c x)) n c
          (levelSet_prop c x) := rfl

/-- The slice chart maps its centre to the origin of the model: `κ y` is fixed
by the straightening, so the recentred hyperplane coordinate of the centre
vanishes. -/
theorem extChartAt_levelSet_center
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) :
    (letI := levelSetChartedSpace hf n c hreg;
      extChartAt (𝓡 n) x₀ x₀) = 0 := by
  show sliceProj (I := I) n (hreg ↑x₀ (levelSet_prop c x₀))
    (adaptedStraightening hf ↑x₀ (hreg ↑x₀ (levelSet_prop c x₀))
      (extChartAt I (↑x₀ : M) ↑x₀) - extChartAt I (↑x₀ : M) ↑x₀) = 0
  rw [adaptedStraightening_center hf ↑x₀ (hreg ↑x₀ (levelSet_prop c x₀)),
    sub_self, map_zero]

/-- In the slice chart at `x₀` and the extended chart of `M` at `↑x₀`, the
inclusion of the level set reads (near the centre) as the smooth map
`z ↦ G⁻¹ (κ y + ι z)` — the straightening inverse composed with the affine
hyperplane parametrization. -/
theorem writtenInExtChartAt_levelSet_val
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) :
    letI := levelSetChartedSpace hf n c hreg
    writtenInExtChartAt (𝓡 n) I x₀ ((↑) : (f ⁻¹' {c} : Set M) → M)
      =ᶠ[𝓝 (extChartAt (𝓡 n) x₀ x₀)]
      (⇑(adaptedStraightening hf ↑x₀ (hreg ↑x₀ (levelSet_prop c x₀))).symm
        ∘ fun w => extChartAt I (↑x₀ : M) ↑x₀
          + sliceEmb (I := I) n (hreg ↑x₀ (levelSet_prop c x₀)) w) := by
  letI := levelSetChartedSpace hf n c hreg
  have hy : f ↑x₀ = c := levelSet_prop c x₀
  have hdf : mfderiv I 𝓘(ℝ, ℝ) f ↑x₀ ≠ 0 := hreg ↑x₀ hy
  have hz₀ : extChartAt (𝓡 n) x₀ x₀ ∈ levelSliceTarget hf ↑x₀ hdf n :=
    (levelSliceChart hf ↑x₀ hdf n c hy).map_source
      (mem_levelChartDomain_self hf ↑x₀ hdf)
  refine Filter.eventuallyEq_of_mem
    ((isOpen_levelSliceTarget hf ↑x₀ hdf n).mem_nhds hz₀) fun z hz => ?_
  have hval : (((extChartAt (𝓡 n) x₀).symm z : (f ⁻¹' {c} : Set M)) : M)
      = (extChartAt I (↑x₀ : M)).symm ((adaptedStraightening hf ↑x₀ hdf).symm
          (extChartAt I (↑x₀ : M) ↑x₀ + sliceEmb (I := I) n hdf z)) := by
    have h0 : (extChartAt (𝓡 n) x₀).symm z
        = (levelSliceChart hf ↑x₀ hdf n c hy).symm z := rfl
    rw [h0]
    exact levelSliceChart_symm_apply hf ↑x₀ hdf n c hy hz
  have hmem : (adaptedStraightening hf ↑x₀ hdf).symm
      (extChartAt I (↑x₀ : M) ↑x₀ + sliceEmb (I := I) n hdf z)
      ∈ (extChartAt I (↑x₀ : M)).target :=
    adaptedStraightening_source_subset hf ↑x₀ hdf
      ((adaptedStraightening hf ↑x₀ hdf).map_target hz)
  show extChartAt I (↑x₀ : M) (((extChartAt (𝓡 n) x₀).symm z :
      (f ⁻¹' {c} : Set M)) : M) = _
  rw [hval, (extChartAt I (↑x₀ : M)).right_inv hmem]
  rfl

/-- **The inclusion of a regular level set is smooth**: with the slice-chart
manifold structure, the inclusion `f ⁻¹' {c} → M` is `C^∞`.  Together with the
fact that it is a topological embedding (being the subtype inclusion), this is
Lee's assertion that the level set is an *embedded* hypersurface. -/
theorem contMDiff_levelSet_val
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := levelSetChartedSpace hf n c hreg
    ContMDiff (𝓡 n) I ∞ ((↑) : (f ⁻¹' {c} : Set M) → M) := by
  letI := levelSetChartedSpace hf n c hreg
  intro x₀
  have hy : f ↑x₀ = c := levelSet_prop c x₀
  have hdf : mfderiv I 𝓘(ℝ, ℝ) f ↑x₀ ≠ 0 := hreg ↑x₀ hy
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hz₀ : extChartAt (𝓡 n) x₀ x₀ ∈ levelSliceTarget hf ↑x₀ hdf n :=
    (levelSliceChart hf ↑x₀ hdf n c hy).map_source
      (mem_levelChartDomain_self hf ↑x₀ hdf)
  have ha : ContDiffAt ℝ ∞
      (fun w : EuclideanSpace ℝ (Fin n) =>
        extChartAt I (↑x₀ : M) ↑x₀ + sliceEmb (I := I) n hdf w)
      (extChartAt (𝓡 n) x₀ x₀) :=
    (contDiff_const.add (sliceEmb (I := I) n hdf).contDiff).contDiffAt
  have hb : ContDiffAt ℝ ∞ (adaptedStraightening hf ↑x₀ hdf).symm
      (extChartAt I (↑x₀ : M) ↑x₀
        + sliceEmb (I := I) n hdf (extChartAt (𝓡 n) x₀ x₀)) :=
    (contDiffOn_adaptedStraightening_symm hf ↑x₀ hdf).contDiffAt
      ((adaptedStraightening hf ↑x₀ hdf).open_target.mem_nhds hz₀)
  have hcomp := hb.comp (extChartAt (𝓡 n) x₀ x₀) ha
  exact ((hcomp.congr_of_eventuallyEq
    (writtenInExtChartAt_levelSet_val hf n c hreg x₀)).contDiffWithinAt)

/-- **The differential of the level-set inclusion, computed**: in the slice
chart at `x₀`, `d(incl)_{x₀} = d(G⁻¹)_{κ y} ∘ ι` — the straightening-inverse
differential applied to the hyperplane embedding. -/
theorem hasMFDerivAt_levelSet_val
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) :
    letI := levelSetChartedSpace hf n c hreg
    HasMFDerivAt (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀
      ((fderiv ℝ (adaptedStraightening hf ↑x₀
          (hreg ↑x₀ (levelSet_prop c x₀))).symm
          (extChartAt I (↑x₀ : M) ↑x₀))
        ∘L sliceEmb (I := I) n (hreg ↑x₀ (levelSet_prop c x₀))) := by
  letI := levelSetChartedSpace hf n c hreg
  have hy : f ↑x₀ = c := levelSet_prop c x₀
  have hdf : mfderiv I 𝓘(ℝ, ℝ) f ↑x₀ ≠ 0 := hreg ↑x₀ hy
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hev := writtenInExtChartAt_levelSet_val hf n c hreg x₀
  have hz0 := extChartAt_levelSet_center hf n c hreg x₀
  rw [hz0] at hev ⊢
  have hι : HasFDerivAt
      (fun w : EuclideanSpace ℝ (Fin n) =>
        extChartAt I (↑x₀ : M) ↑x₀ + sliceEmb (I := I) n hdf w)
      (sliceEmb (I := I) n hdf : EuclideanSpace ℝ (Fin n) →L[ℝ] E) 0 :=
    (sliceEmb (I := I) n hdf).hasFDerivAt.const_add _
  have hι0 : extChartAt I (↑x₀ : M) ↑x₀ + sliceEmb (I := I) n hdf 0
      = extChartAt I (↑x₀ : M) ↑x₀ := by
    rw [map_zero, add_zero]
  have hGs : HasFDerivAt (adaptedStraightening hf ↑x₀ hdf).symm
      (fderiv ℝ (adaptedStraightening hf ↑x₀ hdf).symm
        (extChartAt I (↑x₀ : M) ↑x₀))
      (extChartAt I (↑x₀ : M) ↑x₀ + sliceEmb (I := I) n hdf 0) := by
    rw [hι0]
    have hmemT := extChartAt_self_mem_adaptedStraightening_target hf ↑x₀ hdf
    exact (((contDiffOn_adaptedStraightening_symm hf ↑x₀ hdf).contDiffAt
      ((adaptedStraightening hf ↑x₀ hdf).open_target.mem_nhds
        hmemT)).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hGs.comp (0 : EuclideanSpace ℝ (Fin n)) hι
  exact (hcomp.congr_of_eventuallyEq hev).hasFDerivWithinAt

/-- The differential of the level-set inclusion at `x₀`, as an explicit
continuous linear map. -/
theorem mfderiv_levelSet_val
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) :
    letI := levelSetChartedSpace hf n c hreg
    mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀
      = (fderiv ℝ (adaptedStraightening hf ↑x₀
          (hreg ↑x₀ (levelSet_prop c x₀))).symm
          (extChartAt I (↑x₀ : M) ↑x₀))
        ∘L sliceEmb (I := I) n (hreg ↑x₀ (levelSet_prop c x₀)) := by
  letI := levelSetChartedSpace hf n c hreg
  exact (hasMFDerivAt_levelSet_val hf n c hreg x₀).mfderiv

/-- **The level-set inclusion is an immersion**: its differential is injective
at every point. -/
theorem mfderiv_levelSet_val_injective
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) :
    letI := levelSetChartedSpace hf n c hreg
    Function.Injective
      ⇑(mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀) := by
  letI := levelSetChartedSpace hf n c hreg
  rw [mfderiv_levelSet_val hf n c hreg x₀]
  exact (fderiv_adaptedStraightening_symm_injective hf ↑x₀
    (hreg ↑x₀ (levelSet_prop c x₀))).comp
    (sliceEmb_injective n (hreg ↑x₀ (levelSet_prop c x₀)))

/-- The inclusion differential pairs to zero with `df`: the composite
`f ∘ incl` is the constant `c` on the level set, so `df (d(incl) v) = 0` for
every tangent vector `v` of the level set. -/
theorem mfderivReal_mfderiv_levelSet_val
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) (v : EuclideanSpace ℝ (Fin n)) :
    letI := levelSetChartedSpace hf n c hreg
    mfderivReal (I := I) f ↑x₀
      (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀ v) = 0 := by
  letI := levelSetChartedSpace hf n c hreg
  have hg : MDifferentiableAt I 𝓘(ℝ, ℝ) f ↑x₀ :=
    (hf ↑x₀).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀ :=
    (hasMFDerivAt_levelSet_val hf n c hreg x₀).mdifferentiableAt
  have hchain := mfderiv_comp x₀ hg hval
  have hconst : (f ∘ ((↑) : (f ⁻¹' {c} : Set M) → M)) = fun _ => c :=
    funext fun x => levelSet_prop c x
  rw [hconst, mfderiv_const] at hchain
  have h := ContinuousLinearMap.ext_iff.1 hchain.symm v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at h
  exact h

/-- **The tangent space of the level set is the kernel of the differential**:
the range of the inclusion differential at `x₀` is exactly `ker df_{x₀}`.

This is the identification `T_p M_c = ker df_p` that Lee's Proposition 2.37
needs: paired with `innerAt_grad_eq_zero_of_mem_ker` it says exactly that
`grad f` is normal to the level set.  The inclusion `⊆` follows from
`f ∘ incl = c`; equality is by a dimension count, `d(incl)` being injective
with both sides of dimension `n`.

The proof is routed through the *explicit* composite of `mfderiv_levelSet_val`
rather than through `mfderiv` directly.  The reason is an instance diamond: the
`Module ℝ E` carried by `mfderiv`'s codomain comes from `TangentSpace I ↑x₀`,
not from `NormedSpace ℝ E`, so `Submodule.eq_of_le_of_finrank_eq` cannot
*synthesise* `FiniteDimensional ℝ ↥(ker df)` against it (the two instances are
defeq but not syntactically equal, so even a `haveI` of the clean form does not
match).  Stating the dimension count for the explicit composite, whose
instances all come from `E` itself, makes synthesis succeed; `exact` then
bridges the diamond, since defeq checking — unlike instance search — sees
through it. -/
theorem range_mfderiv_levelSet_val
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) :
    letI := levelSetChartedSpace hf n c hreg
    (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀ :
        EuclideanSpace ℝ (Fin n) →L[ℝ] E).range
      = levelHyperplane (I := I) f ↑x₀ := by
  letI := levelSetChartedSpace hf n c hreg
  have hclean : LinearMap.range
      ((((fderiv ℝ (adaptedStraightening hf ↑x₀ (hreg ↑x₀ (levelSet_prop c x₀))).symm
          (extChartAt I (↑x₀ : M) ↑x₀))
        ∘L sliceEmb (I := I) n (hreg ↑x₀ (levelSet_prop c x₀))) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] E) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E)
      = levelHyperplane (I := I) f ↑x₀ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro u hu
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hu
      have h := mfderivReal_mfderiv_levelSet_val hf n c hreg x₀ v
      rw [mfderiv_levelSet_val hf n c hreg x₀] at h
      exact (mem_levelHyperplane_iff (I := I) f ↑x₀ _).2 h
    · have hinj : Function.Injective
          ⇑((((fderiv ℝ (adaptedStraightening hf ↑x₀
                (hreg ↑x₀ (levelSet_prop c x₀))).symm
              (extChartAt I (↑x₀ : M) ↑x₀))
            ∘L sliceEmb (I := I) n (hreg ↑x₀ (levelSet_prop c x₀))) :
              EuclideanSpace ℝ (Fin n) →L[ℝ] E)) :=
        (fderiv_adaptedStraightening_symm_injective hf ↑x₀
          (hreg ↑x₀ (levelSet_prop c x₀))).comp
          (sliceEmb_injective n (hreg ↑x₀ (levelSet_prop c x₀)))
      rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin,
        finrank_levelHyperplane n (hreg ↑x₀ (levelSet_prop c x₀))]
  rw [mfderiv_levelSet_val hf n c hreg x₀]
  exact hclean

end ChartedSpaceLevelSet

end Poincare.Geometry.Manifold.RegularLevel

end
