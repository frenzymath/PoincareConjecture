import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Affine.ZeroChargeAffineHeightStep
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHypersurfaceCharts

/-!
# Brown's named input on an actual PL-domain frontier

The whole sphere is placed in one actual topological chart. The PL
domain's halfspace charts supply local flatness in those coordinates,
so the named Brown input gives a topological ball with exactly that
image sphere as frontier. No PL filling is asserted. See Hamilton
1976, p.66 and M76 derivation331.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_affine_first_coordinate (ell : V3 →ᴬ[ℝ] ℝ)
    (hell : ell.toAffineMap.linear ≠ 0) :
    ∃ a : V3 ≃ᴬ[ℝ] V3, ∀ x, a x 0 = ell x := by
  obtain ⟨f, _, hfinv⟩ := ZeroChargeJoint.exists_affine_height_coordinates
    (E := Fin 2 → ℝ) ell.toAffineMap hell (by simp) 0
  let q : ((Fin 2 → ℝ) × ℝ) ≃L[ℝ] V3 :=
    (ContinuousLinearEquiv.prodComm ℝ (Fin 2 → ℝ) ℝ).trans
      (Fin.consEquivL ℝ (fun _ : Fin 3 => ℝ))
  refine ⟨f.symm.trans q.toContinuousAffineEquiv, ?_⟩
  intro x
  change (f.symm x).2 = ell x
  have hx := hfinv x
  change (f.symm x).2 = ell x - 0 at hx
  simpa only [sub_zero] using hx

variable {X : Type*} [TopologicalSpace X] {ι : Type*}

/-- The complete frontier sphere of an actual PL domain is locally
flat after placing it in one topological chart. The halfspace charts
provide the flattening; no local-flatness hypothesis on the sphere
map is added. See Hamilton p.66 and derivation331. -/
theorem PLDomain.locallyFlat_frontier_image
    {e : ι → OpenPartialHomeomorph X V3} {K : Set X}
    (hK : PLDomain e K) (s : ChartwisePLSphere e (frontier K))
    (c : OpenPartialHomeomorph X V3) (hsource : frontier K ⊆ c.source) :
    Nonempty (LocallyFlatTopologicalSphere (c '' frontier K)) := by
  let sc : frontier K ≃ₜ c '' frontier K :=
    c.homeomorphOfImageSubsetSource hsource rfl
  refine ⟨⟨s.parametrization.trans sc, ?_⟩⟩
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨ell, v, B, hv, hzB, _, _, hhalf⟩ := hK.halfspace z hz
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hzero
    have hv' : ell.toAffineMap.linear v = 1 := hv
    rw [hzero] at hv'
    norm_num at hv'
  obtain ⟨a, ha⟩ := exists_affine_first_coordinate ell hell
  let D := (c.symm.trans B).trans a.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨D, ?_, ?_⟩
  · change (c z ∈ c.target ∧ c.symm (c z) ∈ B.source) ∧ _
    refine ⟨⟨c.map_source (hsource hz), ?_⟩, mem_univ _⟩
    rwa [c.left_inv (hsource hz)]
  · intro y hy
    have hyc : y ∈ c.target := hy.1.1
    have hyB : c.symm y ∈ B.source := hy.1.2
    have hmem : y ∈ c '' frontier K ↔ c.symm y ∈ frontier K := by
      constructor
      · rintro ⟨w, hw, rfl⟩
        rwa [c.left_inv (hsource hw)]
      · intro hw
        exact ⟨c.symm y, hw, c.right_inv hyc⟩
    change y ∈ c '' frontier K ↔ a (B (c.symm y)) 0 = 0
    rw [ha]
    have hfront := B.isImage_frontier_of_affine_nonneg ell hell hhalf
    exact hmem.trans (hfront.apply_mem_iff hyB).symm

/-- Apply the named Brown theorem to the literal coordinate image of
the whole PL-domain frontier. The conclusion is only a compact
topological ball pair; compatibility of a new filling atlas is a
subsequent construction. See Hamilton p.66 and derivation331. -/
theorem PLDomain.exists_brown_ball_in_frontier_chart
    (brown : HasBrownLocallyFlatSphereBalls)
    {e : ι → OpenPartialHomeomorph X V3} {K : Set X}
    (hK : PLDomain e K) (s : ChartwisePLSphere e (frontier K))
    (c : OpenPartialHomeomorph X V3) (hsource : frontier K ⊆ c.source) :
    ∃ D : Set V3, IsCompact D ∧ frontier D = c '' frontier K ∧
      IsUnitBallPair V3 D (c '' frontier K) :=
  brown _ (hK.locallyFlat_frontier_image s c hsource)

end PoincareMT.M76
