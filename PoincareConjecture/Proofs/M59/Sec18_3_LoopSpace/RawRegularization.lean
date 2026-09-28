import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RegularRepresentatives
import PoincareConjecture.Proofs.M59.Mathlib.CubeSphereHomotopy










set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m59_raw_regularization_of_pole_path (q : M59SphereQuotient) (x : M)
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (p : Path (F q.pole) (constantC1Loop x)) :
    ∃ Gamma : FreeTwoSphereFamily (M := M),
      M59NormalizedAt q x Gamma ∧ F.Homotopic (m59FamilyMap Gamma) := by
  let a : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (F q.pole) :=
    ⟨F.comp q.map, fun z hz => congrArg F (q.boundary_collapsed z hz)⟩
  let b := GenLoop.boundaryTransport p a
  let G := q.descend b
  have hbase : G q.pole = constantC1Loop x := q.descend_pole b
  have hnull := m59SphereMap_null_of_pole q x G hbase
  let Gamma := m59RadialSphereFamily q x G hbase hnull
  have H : F.Homotopic G := (GenLoop.boundaryTransportHomotopy p a).descend_sphere
    q.map q.surjective q.exact_fibers F G (fun _ => rfl)
    (fun z => (q.descend_map b z).symm)
  refine ⟨Gamma, m59RadialSphereFamily_normalized q x G hbase hnull, H.trans ?_⟩
  exact ⟨m59RadialLoopHomotopy.compContinuousMap G⟩

end PoincareConjecture
