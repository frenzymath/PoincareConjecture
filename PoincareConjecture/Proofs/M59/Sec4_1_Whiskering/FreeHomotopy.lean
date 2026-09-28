import PoincareConjecture.Proofs.M59.Sec4_1_Whiskering.Service
import PoincareConjecture.Proofs.M59.Mathlib.CubeSphereHomotopy











set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



def m59FamilyCube (Gamma : FreeTwoSphereFamily (M := M)) :
    GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop Gamma.basepoint) :=
  ⟨Gamma.class_certificate.cube_representative, Gamma.class_certificate.boundary_const⟩




theorem whisker_constantLoopPath_freeHomotopic
    (q : M59SphereQuotient) (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : Gamma.class_certificate.sphere_parameter = q.map)
    (hDelta : Delta.class_certificate.sphere_parameter = q.map)
    (p : Path Gamma.basepoint Delta.basepoint) (P : M59ConstantLoopPath p)
    (hclass : (m59HigherBasepointTransport (C1FreeLoopSpace (M := M)) 2).map
      P.loop Gamma.homotopy_class = Delta.homotopy_class) :
    (m59FamilyMap Gamma).Homotopic (m59FamilyMap Delta) := by
  have hclasses : (⟦GenLoop.boundaryTransport P.loop (m59FamilyCube Gamma)⟧ :
      HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop Delta.basepoint)) =
        ⟦m59FamilyCube Delta⟧ := by
    change (m59HigherBasepointTransport (C1FreeLoopSpace (M := M)) 2).map P.loop
      (Quotient.mk' (m59FamilyCube Gamma)) = Quotient.mk' (m59FamilyCube Delta)
    exact (congrArg ((m59HigherBasepointTransport (C1FreeLoopSpace (M := M)) 2).map P.loop)
      Gamma.class_certificate.class_eq.symm).trans (hclass.trans Delta.class_certificate.class_eq)
  obtain ⟨K⟩ : GenLoop.Homotopic
      (GenLoop.boundaryTransport P.loop (m59FamilyCube Gamma)) (m59FamilyCube Delta) :=
    Quotient.exact hclasses
  let H := (GenLoop.boundaryTransportHomotopy P.loop (m59FamilyCube Gamma)).trans
    (GenLoop.HomotopyAlong.ofRel K)
  apply H.descend_sphere q.map q.surjective q.exact_fibers
  · intro v
    change Gamma.class_certificate.cube_representative v = Gamma.family (q.map v)
    rw [← hGamma]
    exact Gamma.class_certificate.family_agreement v
  · intro v
    change Delta.class_certificate.cube_representative v = Delta.family (q.map v)
    rw [← hDelta]
    exact Delta.class_certificate.family_agreement v

end PoincareConjecture
