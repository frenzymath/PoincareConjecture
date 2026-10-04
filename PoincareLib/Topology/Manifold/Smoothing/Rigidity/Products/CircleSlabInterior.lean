import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.CircleSlabDomain

/-!+# Actual interior points on both sides of the regular circle slab

Surjectivity supplies the midpoint fiber and the omitted zero
fiber. Their whole open preimages give interior witnesses in the
original slab and its closed exterior. See rigidity053, section4.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

/-- The midpoint of the actual open target arc supplies an interior
point of the literal original slab. See rigidity053, section4. -/
theorem circle_slab_interior_nonempty
    {X : Type*} [TopologicalSpace X] (p : ℝ) [Fact (0 < p)]
    (q : C(X, AddCircle p)) (hq : Function.Surjective q)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p) :
    (interior (q ⁻¹' AddCircle.closedIntervalArc p a b)).Nonempty := by
  let A := AddCircle.closedIntervalArc p a b
  have hmid : (((a + b) / 2 : ℝ) : AddCircle p) ∈ interior A := by
    rw [AddCircle.interior_closedIntervalArc p ha hb]
    exact ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨x, hx⟩ := hq (((a + b) / 2 : ℝ) : AddCircle p)
  have hopen : IsOpen (q ⁻¹' interior A) := isOpen_interior.preimage q.continuous
  have hsub : q ⁻¹' interior A ⊆ interior (q ⁻¹' A) :=
    hopen.subset_interior_iff.mpr (preimage_mono interior_subset)
  exact ⟨x, hsub (by change q x ∈ interior A; rw [hx]; exact hmid)⟩

/-- The actual zero fiber lies in the open complement of the
closed slab, hence inside its closed exterior. See053, section4. -/
theorem circle_slab_exterior_interior_nonempty
    {X : Type*} [TopologicalSpace X] (p : ℝ) [Fact (0 < p)]
    (q : C(X, AddCircle p)) (hq : Function.Surjective q)
    {a b : ℝ} (ha : 0 < a) (hb : b < p) :
    (interior (interior (q ⁻¹' AddCircle.closedIntervalArc p a b))ᶜ).Nonempty := by
  let R := q ⁻¹' AddCircle.closedIntervalArc p a b
  have hR : IsClosed R :=
    (AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage q.continuous
  obtain ⟨x, hx⟩ := hq 0
  have hxR : x ∈ Rᶜ := by
    intro h
    have hzero : (0 : AddCircle p) ∈ AddCircle.closedIntervalArc p a b := by
      change q x ∈ AddCircle.closedIntervalArc p a b at h
      rwa [hx] at h
    exact AddCircle.zero_notMem_closedIntervalArc p ha hb hzero
  have hsub : Rᶜ ⊆ interior (interior R)ᶜ :=
    hR.isOpen_compl.subset_interior_iff.mpr (compl_subset_compl.mpr interior_subset)
  exact ⟨x, hsub hxR⟩

/-- The original domain and its literal closed exterior meet in
precisely the complete original frontier. See rigidity053, section5. -/
theorem PLDomain.inter_closed_exterior
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) : R ∩ (interior R)ᶜ = frontier R := by
  rw [he.closed.frontier_eq]
  rfl

end PoincareMT.M76
