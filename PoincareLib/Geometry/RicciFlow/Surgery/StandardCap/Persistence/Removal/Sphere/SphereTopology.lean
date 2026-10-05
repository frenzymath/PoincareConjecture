import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Topology
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Topology.CoveringNullhomotopy
import PoincareLib.AlgebraicTopology.SingularHomology.Sphere.IntegralSphereBase
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The topological obstruction for the collar sphere

The published integral homology of the two-sphere excludes a
contraction. Homotopy lifting then rules out a nullhomotopic local
homeomorphism from that sphere to a Hausdorff neck cross-section.
Morgan--Tian, Claim 16.10, pp. 374-375; see M44 derivation 45.
-/

set_option autoImplicit false

open scoped ContinuousMap

namespace PoincareMT.M44

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The actual standard two-sphere is not contractible, by its
published nonzero integral second homology. Source: Claim 16.10's
sphere-in-neck contradiction; M44 derivation 45. -/
theorem sphere_two_not_contractible : ¬ ContractibleSpace S2 := by
  intro h
  let : ContractibleSpace S2 := h
  have hz := Proofs.M02.Topology.integral_contractible_homology_isZero S2 2 (by decide)
  have hzZ := hz.of_iso Proofs.M02.Topology.integralSphereH2Iso.symm
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hzZ
  have h01 := hsub.elim (0 : ULift ℤ) 1
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (congrArg ULift.down h01)

/-- A local homeomorphism from the actual collar sphere cannot
extend to a nullhomotopy in its Hausdorff target. Source: Claim 16.10,
pp. 374-375; M44 derivation 45. -/
theorem sphere_localHomeomorph_not_nullhomotopic
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : C(S2, X)) (hf : IsLocalHomeomorph f) : ¬ f.Nullhomotopic := by
  let : PathConnectedSpace S2 := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  intro hn
  exact sphere_two_not_contractible
    ((isLocalHomeomorph_iff_isCoveringMap.mp hf).contractibleSpace_of_nullhomotopic f hn)

end PoincareMT.M44
