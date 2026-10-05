import PoincareLib.Topology.Homotopy.LoopSpace.Evaluation
import PoincareLib.Topology.Homotopy.LoopSpace.Family
import PoincareLib.Topology.Homotopy.LoopSpace.SphereNullhomotopy

/-!
# The raw terminal step of Lemma 18.27

The constant-loop family at the end of Morgan--Tian's contraction is freely
nullhomotopic when the connected manifold has trivial pi2 at the given
basepoint. This file uses the raw continuous-map interface of M58.
It does not yet construct the short-loop contraction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.LoopSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M]

/-- Every raw sphere map in a connected manifold with the given trivial
pi2 is homotopic to the chosen constant. Source: MT Lemma 18.27, p. 434. -/
theorem loopTwoSphere_homotopic_const
    (hconnected : IsConnected (Set.univ : Set M)) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) (f : C(LoopTwoSphere, M)) :
    f.Homotopic (ContinuousMap.const _ x) := by
  let : ConnectedSpace M := connectedSpace_iff_univ.mpr hconnected
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace LoopAmbient M
  let : PathConnectedSpace M := .of_locallyPathConnectedSpace
  let e : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  have h := sphere_homotopic_const_of_pi_trivial 1 x hpi (f.comp (e : C(_, _)))
  have h' := h.comp (ContinuousMap.Homotopic.refl
    (e.symm : C(LoopTwoSphere, Metric.sphere (0 : LoopAmbient) 1)))
  simpa only [ContinuousMap.comp_assoc, Homeomorph.toContinuousMap_comp_symm,
    ContinuousMap.comp_id, ContinuousMap.const_comp] using h'

variable [IsManifold (𝓡 3) ∞ M]

/-- The variable family of constant loops is homotopic to the prescribed
constant-loop family. Source: the last paragraph of MT Lemma 18.27, p. 434. -/
theorem constant_loop_family_homotopic
    (hconnected : IsConnected (Set.univ : Set M)) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) (f : C(LoopTwoSphere, M)) :
    (constantLoopMap.comp f).Homotopic (constantLoopFamily x) := by
  exact (ContinuousMap.Homotopic.refl constantLoopMap).comp
    (loopTwoSphere_homotopic_const hconnected x hpi f)

/-- A raw family contracted to constant loops at its evaluation points is
nullhomotopic at the chosen basepoint. Source: MT Lemma 18.27, p. 434. -/
theorem raw_family_homotopic_const_of_contraction
    (hconnected : IsConnected (Set.univ : Set M)) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) (z : LoopCircle)
    (source : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (H : source.Homotopic (constantLoopMap.comp ((loopEvaluation z).comp source))) :
    source.Homotopic (constantLoopFamily x) :=
  H.trans (constant_loop_family_homotopic hconnected x hpi ((loopEvaluation z).comp source))

end PoincareMT.LoopSpace
