import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHypersurfaceCharts

/-!
# The opposite closed domain in the original PL atlas

The literal nondegenerate halfspace equation identifies the interior
with its positive side. Negating its scalar and slope vector therefore
constructs the opposite closed PL domain, with exactly the same whole
frontier. See Hatcher Corollary3.3, p48, and Wall derivation004, section3.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An actual nonconstant affine halfspace chart identifies the whole
local interior with its strictly positive side. See Wall004, section3. -/
theorem mem_interior_iff_affine_pos (H : OpenPartialHomeomorph X E)
    {P : Set X} (ell : E →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    (hhalf : ∀ x ∈ H.source, x ∈ P ↔ 0 ≤ ell (H x))
    {x : X} (hx : x ∈ H.source) : x ∈ interior P ↔ 0 < ell (H x) := by
  have hfront := H.isImage_frontier_of_affine_nonneg ell hell hhalf
  constructor
  · intro hi
    have hp : x ∈ P := interior_subset hi
    have hn : x ∉ frontier P := (mem_interior_iff_notMem_frontier hp).mp hi
    refine lt_of_le_of_ne ((hhalf x hx).mp hp) ?_
    intro hz
    exact hn ((hfront.apply_mem_iff hx).mp hz.symm)
  · intro hpos
    have hp : x ∈ P := (hhalf x hx).mpr hpos.le
    apply (mem_interior_iff_notMem_frontier hp).mpr
    intro hf
    exact (ne_of_gt hpos) ((hfront.apply_mem_iff hx).mpr hf)

end OpenPartialHomeomorph

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The complement of the actual interior is a closed PL domain in
the same original atlas and has the identical whole frontier.
Both claims are produced from the original slope-one halfspace charts.
See Wall004, section3. -/
theorem PLDomain.compl_interior
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {P : Set X}
    (hP : PLDomain e P) :
    PLDomain e (interior P)ᶜ ∧ frontier (interior P)ᶜ = frontier P := by
  have hboundary : ∀ x ∈ frontier P,
      ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (H : OpenPartialHomeomorph X V3),
        ell.contLinear v = 1 ∧ x ∈ H.source ∧ ell (H x) = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y ∈ H.source, y ∈ (interior P)ᶜ ↔ 0 ≤ ell (H y) := by
    intro x hx
    obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := hP.halfspace x hx
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h] at hval
      norm_num at hval
    refine ⟨-ell, -v, H, ?_, hxH, ?_, hcompat, ?_⟩
    · simp only [ContinuousAffineMap.neg_contLinear, neg_apply,
        map_neg, neg_neg, hv]
    · change -ell (H x) = 0
      rw [hzero, neg_zero]
    · intro y hy
      change y ∉ interior P ↔ 0 ≤ -ell (H y)
      rw [H.mem_interior_iff_affine_pos ell hell hhalf hy]
      exact not_lt.trans neg_nonneg.symm
  have hsub : frontier (interior P)ᶜ ⊆ frontier P := by
    rw [frontier_compl]
    exact frontier_interior_subset
  refine ⟨⟨hP.cover, hP.compatible, isOpen_interior.isClosed_compl,
    fun x hx => hboundary x (hsub hx)⟩, Subset.antisymm hsub ?_⟩
  intro x hx
  obtain ⟨ell, v, H, hv, hxH, hzero, _, hhalf⟩ := hboundary x hx
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    norm_num at hval
  exact ((H.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff hxH).mp hzero

end PoincareMT.M76
