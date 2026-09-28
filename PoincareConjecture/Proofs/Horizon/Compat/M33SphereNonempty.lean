import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry



namespace PoincareConjecture

instance m33UnitTwoSphereNonempty : Nonempty UnitTwoSphere :=
  ⟨⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩⟩

end PoincareConjecture
