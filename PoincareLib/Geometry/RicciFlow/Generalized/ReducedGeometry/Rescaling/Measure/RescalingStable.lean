import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Geometry.RescalingBranches
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Geometry.RescalingDifferential
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StableDomain

/-!
# Full stable carriers under parabolic rescaling

Morgan-Tian Definition 6.25 and Corollary 6.74, pp. 116, 142. The
normalized linear homeomorphism transports the full open neighborhood
of unique minimizing branches and actual differential invertibility.
-/

set_option autoImplicit false
-- The rescaled spacetime retains the original actual point type.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

include hCoordinates in
/-- The full stable-initial-vector predicate is invariant under the
normalized initial equivalence. Corollary 6.74, p. 142. -/
theorem rescalingStableInitialVector_iff {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x) :
    M14StableInitialVector G T τ x E Z ↔
      M14StableInitialVector (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * τ) x E'
          (rescalingInitialEquiv G.spacetime Q hQ a x Z) := by
  let A := rescalingInitialEquiv G.spacetime Q hQ a x
  have hdom : (Z, Real.sqrt τ) ∈ E.domain ↔ (A Z, Real.sqrt (Q * τ)) ∈ E'.domain := by
    simpa only [Real.sqrt_mul hQ.le] using
      rescalingExponential_domain_iff hCoordinates hM12 hM13 G Q hQ a E E' Z (Real.sqrt τ)
  have hbij (hs : (Z, Real.sqrt τ) ∈ E.domain)
      (hs' : (A Z, Real.sqrt (Q * τ)) ∈ E'.domain) :
      Function.Bijective (E'.differential (A Z) (Real.sqrt (Q * τ)) hs') ↔
        Function.Bijective (E.differential Z (Real.sqrt τ) hs) := by
    revert hs'
    rw [Real.sqrt_mul hQ.le]
    intro hs'
    exact rescalingDifferential_bijective_iff hCoordinates hM12 hM13 G Q hQ a E E'
      Z (Real.sqrt τ) hs hs'
  constructor
  · rintro ⟨hs, hb, U, hU, hZ, hbranch⟩
    refine ⟨hdom.mp hs, (hbij hs (hdom.mp hs)).mpr hb,
      A.symm ⁻¹' U, hU.preimage A.symm.continuous, ?_, ?_⟩
    · simpa only [mem_preimage, A, ContinuousLinearEquiv.symm_apply_apply] using hZ
    · intro W hW
      have h := (rescalingUniqueBranch_iff hCoordinates hM12 hM13 G Q hQ a E E'
        (A.symm W)).mp (hbranch _ hW)
      simpa only [A, ContinuousLinearEquiv.apply_symm_apply] using h
  · rintro ⟨hs', hb, U, hU, hZ, hbranch⟩
    refine ⟨hdom.mpr hs', (hbij (hdom.mpr hs') hs').mp hb,
      A ⁻¹' U, hU.preimage A.continuous, hZ, ?_⟩
    intro W hW
    exact (rescalingUniqueBranch_iff hCoordinates hM12 hM13 G Q hQ a E E' W).mpr
      (hbranch _ hW)

/-- A supplied source stable set supplies a point totalizing the actual
target endpoint map, even if its carrier is empty. Definition 6.25 and
Corollary 6.74, pp. 116, 142. -/
noncomputable def rescalingStableSet {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E) :
    M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E' := by
  let q₀ := H.endpoint_slice_map 0
  let q₀' : ((rescalingTransport hM12 hM13 G Q hQ a).slices
      (parabolicTime Q a T - Q * τ)).Point := ⟨q₀.val, by
    change parabolicTime Q a (G.spacetime.timeFunction q₀.val) = parabolicTime Q a T - Q * τ
    rw [q₀.property]
    unfold parabolicTime
    ring⟩
  exact stableSetOfSlicePoint E' (mul_pos hQ H.tau_pos) q₀'

include hCoordinates in
/-- Any two full frozen source and target stable records have precisely
corresponding carriers. Corollary 6.74, p. 142. -/
theorem rescalingStable_carrier_iff {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (H : M14StableSet G T τ x E)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E') (Z : G.Horizontal x) :
    Z ∈ H.carrier ↔ rescalingInitialEquiv G.spacetime Q hQ a x Z ∈ H'.carrier := by
  rw [H.carrier_exact, H'.carrier_exact]
  exact rescalingStableInitialVector_iff hCoordinates hM12 hM13 G Q hQ a E E' Z

end PoincareMT.M14
