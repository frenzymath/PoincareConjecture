import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Central projection of linearly independent simplices

The convex hull of linearly independent position vectors is disjoint from
the origin. Normalization identifies each finite such simplex with its
spherical image. This is the simplex calculation in Cairns 1940,
Sections 5--6, pp. 801--802. See M76 derivation 16.
-/

set_option autoImplicit false

open Set NormedSpace

section LinearExtension

variable {𝕜 E F ι : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] {v : ι → E}

/-- Any values on a linearly independent family extend to a linear map.
This supplies the separating functional for central projection;
see Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.exists_linearMap_apply_eq (hv : LinearIndependent 𝕜 v) (f : ι → F) :
    ∃ L : E →ₗ[𝕜] F, ∀ i, L (v i) = f i := by
  classical
  let b := Module.Basis.span hv
  obtain ⟨L, hL⟩ := (b.constr ℤ f).exists_extend
  refine ⟨L, fun i => ?_⟩
  have h := LinearMap.congr_fun hL (b i)
  rw [Module.Basis.constr_basis] at h
  simpa [b] using h

end LinearExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear functional constant on a set is constant on its convex hull.
See the affine-level-set argument in M76 derivation 16. -/
theorem LinearMap.eqOn_const_convexHull (L : E →ₗ[ℝ] ℝ) {s : Set E} {c : ℝ}
    (hs : ∀ x ∈ s, L x = c) : ∀ x ∈ convexHull ℝ s, L x = c :=
  convexHull_min hs ((convex_singleton c).linear_preimage L)

/-- A simplex of linearly independent position vectors lies on a linear
functional's level set at one. See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.exists_eq_one_on_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    ∃ L : E →ₗ[ℝ] ℝ, ∀ x ∈ convexHull ℝ s, L x = 1 := by
  obtain ⟨L, hL⟩ := hs.exists_linearMap_apply_eq (fun _ => (1 : ℝ))
  exact ⟨L, L.eqOn_const_convexHull (fun x hx => hL ⟨x, hx⟩)⟩

/-- The origin is outside the convex hull of linearly independent
position vectors. See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.zero_notMem_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) : (0 : E) ∉ convexHull ℝ s := by
  obtain ⟨L, hL⟩ := hs.exists_eq_one_on_convexHull
  intro hzero
  simpa using hL 0 hzero

/-- Normalization is continuous at each nonzero vector.
See the central projection in Cairns p. 802 and M76 derivation 16. -/
theorem continuousAt_normalize_of_ne_zero {x : E} (hx : x ≠ 0) :
    ContinuousAt (normalize : E → E) x :=
  (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

/-- Central projection is injective on any set contained in a linear
functional's level set at one. See M76 derivation 16. -/
theorem LinearMap.injOn_normalize_of_eq_one (L : E →ₗ[ℝ] ℝ) {s : Set E}
    (hs : ∀ x ∈ s, L x = 1) : InjOn (normalize : E → E) s := by
  intro x hx y hy hxy
  have hnorm : ‖x‖ = ‖y‖ := by
    have h := congrArg L hxy
    simp only [NormedSpace.normalize, map_smul, hs x hx, hs y hy, smul_eq_mul, mul_one] at h
    exact inv_injective h
  calc
    x = ‖x‖ • normalize x := (norm_smul_normalize x).symm
    _ = ‖y‖ • normalize y := by rw [hnorm, hxy]
    _ = y := norm_smul_normalize y

/-- Central projection is injective on a simplex of linearly independent
position vectors. See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.injOn_normalize_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    InjOn (normalize : E → E) (convexHull ℝ s) := by
  obtain ⟨L, hL⟩ := hs.exists_eq_one_on_convexHull
  exact L.injOn_normalize_of_eq_one hL

/-- All points of the projected simplex lie on the unit sphere.
See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.normalize_convexHull_subset_sphere {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    NormedSpace.normalize '' convexHull ℝ s ⊆ Metric.sphere (0 : E) 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_sphere, dist_zero_right]
  exact norm_normalize (fun h => hs.zero_notMem_convexHull (h ▸ hx))

/-- A finite simplex of independent position vectors is homeomorphic to
its spherical image under central projection. See Cairns p. 802 and
M76 derivation 16. -/
noncomputable def LinearIndependent.radialSimplexHomeomorph {s : Finset E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    convexHull ℝ (s : Set E) ≃ₜ NormedSpace.normalize '' convexHull ℝ (s : Set E) := by
  letI : CompactSpace (convexHull ℝ (s : Set E)) :=
    isCompact_iff_compactSpace.mp (s.finite_toSet.isCompact_convexHull ℝ)
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn _ _ hs.injOn_normalize_convexHull)
  have hc : ContinuousOn (NormedSpace.normalize : E → E) (convexHull ℝ (s : Set E)) := by
    intro x hx
    exact (continuousAt_normalize_of_ne_zero
      (fun h => hs.zero_notMem_convexHull (h ▸ hx))).continuousWithinAt
  exact hc.domRestrict.subtype_mk _

/-- The central-projection homeomorphism agrees with normalization.
See M76 derivation 16. -/
theorem LinearIndependent.radialSimplexHomeomorph_apply {s : Finset E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) (x : convexHull ℝ (s : Set E)) :
    (hs.radialSimplexHomeomorph x : E) = normalize x.val := rfl
