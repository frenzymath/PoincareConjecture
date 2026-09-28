import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth









set_option autoImplicit false

namespace PoincareConjecture.Proofs.M61


instance loopTwoSphereCompactSpace : CompactSpace LoopTwoSphere := by
  let e : (Metric.sphere (0 : LoopAmbient) 1) ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  exact e.compactSpace


instance loopTwoSphereNonempty : Nonempty LoopTwoSphere :=
  ⟨⟨EuclideanSpace.basisFun (Fin 3) ℝ 0,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0⟩⟩

end PoincareConjecture.Proofs.M61
