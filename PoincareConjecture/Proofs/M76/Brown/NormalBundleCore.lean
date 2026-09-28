import PoincareConjecture.Proofs.M76.Brown.NormalPairAtlas
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false

open Set Bundle

namespace BrownCollar.FlatteningAtlas

variable {X P ι : Type*} [TopologicalSpace X] [NormedAddCommGroup P]
  [NormedSpace ℝ P] {S : Set X} (A : FlatteningAtlas P S ι)

noncomputable def transitionUnit (i j : ι) (x : S) : SignTypeˣ :=
  Units.mk0 (A.transitionSign i j x) (A.transitionSign_ne_zero i j x)

theorem transitionUnit_self (i : ι) (x : S) (hx : x ∈ A.baseSet i) :
    A.transitionUnit i i x = 1 := by
  apply Units.ext
  exact A.transitionSign_self i x hx

theorem transitionUnit_cocycle (i j k : ι) (x : S)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j ∩ A.baseSet k) :
    A.transitionUnit j k x * A.transitionUnit i j x = A.transitionUnit i k x := by
  apply Units.ext
  exact A.transitionSign_cocycle i j k x hx

theorem continuousOn_transitionUnit (i j : ι) :
    ContinuousOn (A.transitionUnit i j) (A.baseSet i ∩ A.baseSet j) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply Units.continuous_iff.mpr
  constructor
  · exact (A.continuousOn_transitionSign i j).domRestrict
  · exact (A.continuousOn_transitionSign i j).domRestrict

noncomputable def normalBundleCore : FiberBundleCore ι S SignTypeˣ where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_source_at
  coordChange i j x v := A.transitionUnit i j x * v
  coordChange_self i x hx v := by rw [A.transitionUnit_self i x hx, one_mul]
  continuousOn_coordChange i j :=
    ((A.continuousOn_transitionUnit i j).comp continuous_fst.continuousOn
      (fun _ h => h.1)).mul continuous_snd.continuousOn
  coordChange_comp i j k x hx v := by
    rw [← mul_assoc, A.transitionUnit_cocycle i j k x hx]

theorem normalBundle_isCoveringMap : IsCoveringMap A.normalBundleCore.proj :=
  FiberBundle.isCoveringMap

end BrownCollar.FlatteningAtlas
