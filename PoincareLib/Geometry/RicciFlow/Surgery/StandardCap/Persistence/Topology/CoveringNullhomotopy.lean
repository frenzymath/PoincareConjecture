import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible

/-!
# A nullhomotopic covering contracts its connected domain

Lift the nullhomotopy from the identity. Connectedness makes its
terminal map, which lands in one fiber, constant. This is the
topological step in Morgan--Tian, Claim 16.10, pp. 374-375;
see M44 derivation 45.
-/

set_option autoImplicit false

open scoped ContinuousMap

namespace IsCoveringMap

/-- A nonempty connected domain of a nullhomotopic covering map is
contractible. Source: the covering-space proof of the sphere-in-neck
contradiction in Claim 16.10; M44 derivation 45. -/
theorem contractibleSpace_of_nullhomotopic
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Nonempty E] [PreconnectedSpace E] (f : C(E, X))
    (hf : IsCoveringMap f) (hnull : f.Nullhomotopic) : ContractibleSpace E := by
  classical
  obtain ⟨y, ⟨H⟩⟩ := hnull
  let e0 : E := Classical.ofNonempty
  have hzero : ∀ e, H.toContinuousMap (0, e) = f ((ContinuousMap.id E) e) :=
    fun e => H.apply_zero e
  let L := hf.liftHomotopy H.toContinuousMap (ContinuousMap.id E) hzero
  have hlift (e : E) : f (L (1, e)) = y :=
    (congrFun (hf.liftHomotopy_lifts H.toContinuousMap (ContinuousMap.id E) hzero)
      (1, e)).trans (H.apply_one e)
  have hterminal (e : E) : L (1, e) = L (1, e0) :=
    hf.const_of_comp (L.continuous.comp (continuous_const.prodMk continuous_id))
      (fun a b => (hlift a).trans (hlift b).symm) e e0
  apply (contractible_iff_id_nullhomotopic E).mpr
  refine ⟨L (1, e0), ⟨{
    toContinuousMap := L
    map_zero_left := ?_
    map_one_left := hterminal
  }⟩⟩
  exact hf.liftHomotopy_zero H.toContinuousMap (ContinuousMap.id E) hzero

end IsCoveringMap
