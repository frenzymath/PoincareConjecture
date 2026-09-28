import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology
import PoincareConjecture.Proofs.M58.Mathlib.SphereNullhomotopy

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M]

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

theorem constant_loop_family_homotopic
    (hconnected : IsConnected (Set.univ : Set M)) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) (f : C(LoopTwoSphere, M)) :
    (constantLoopMap.comp f).Homotopic (constantLoopFamily x) := by
  exact (ContinuousMap.Homotopic.refl constantLoopMap).comp
    (loopTwoSphere_homotopic_const hconnected x hpi f)

theorem raw_family_homotopic_const_of_contraction
    (hconnected : IsConnected (Set.univ : Set M)) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) (z : LoopCircle)
    (source : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (H : source.Homotopic (constantLoopMap.comp ((loopEvaluation z).comp source))) :
    source.Homotopic (constantLoopFamily x) :=
  H.trans (constant_loop_family_homotopic hconnected x hpi ((loopEvaluation z).comp source))

end PoincareConjecture.Proofs.M58
