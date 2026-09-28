import PoincareConjecture.Proofs.M44.Mathlib.CoveringNullhomotopy
import PoincareConjecture.Proofs.M02.Topology.IntegralSphereBase
import Mathlib.Analysis.Normed.Module.Connected










set_option autoImplicit false

open scoped ContinuousMap

namespace PoincareConjecture.M44

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1




theorem sphere_two_not_contractible : ¬ ContractibleSpace S2 := by
  intro h
  let : ContractibleSpace S2 := h
  have hz := Proofs.M02.Topology.integral_contractible_homology_isZero S2 2 (by decide)
  have hzZ := hz.of_iso Proofs.M02.Topology.integralSphereH2Iso.symm
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hzZ
  have h01 := hsub.elim (0 : ULift ℤ) 1
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (congrArg ULift.down h01)




theorem sphere_localHomeomorph_not_nullhomotopic
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : C(S2, X)) (hf : IsLocalHomeomorph f) : ¬ f.Nullhomotopic := by
  let : PathConnectedSpace S2 := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  intro hn
  exact sphere_two_not_contractible
    ((isLocalHomeomorph_iff_isCoveringMap.mp hf).contractibleSpace_of_nullhomotopic f hn)

end PoincareConjecture.M44
