import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.Postcomposition
import PoincareConjecture.Definitions.Ch15.SurgeryComparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u

namespace PoincareConjecture

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

def m59PostcomposeFamily (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (L : M59LoopPostcomposition f) (Gamma : FreeTwoSphereFamily (M := M)) :
    FreeTwoSphereFamily (M := N) where
  basepoint := f Gamma.basepoint
  family := fun c => L.map (Gamma.family c)
  homotopy_class := surgeryHomotopyMap L.map (L.maps_constant Gamma.basepoint)
    Gamma.homotopy_class
  class_certificate := {
    cube_representative := L.map.comp Gamma.class_certificate.cube_representative
    boundary_const := fun z hz => by
      change L.map (Gamma.class_certificate.cube_representative z) = _
      rw [Gamma.class_certificate.boundary_const z hz, L.maps_constant]
    sphere_parameter := Gamma.class_certificate.sphere_parameter
    sphere_parameter_surjective := Gamma.class_certificate.sphere_parameter_surjective
    sphere_parameter_boundary_collapsed :=
      Gamma.class_certificate.sphere_parameter_boundary_collapsed
    sphere_parameter_quotient_fiber := Gamma.class_certificate.sphere_parameter_quotient_fiber
    family_agreement := fun z => congrArg L.map (Gamma.class_certificate.family_agreement z)
    class_eq := congrArg
      (surgeryHomotopyMap L.map (L.maps_constant Gamma.basepoint))
      Gamma.class_certificate.class_eq }
  continuous := L.map.continuous.comp Gamma.continuous
  derivative_continuous := fun i => by
    have heq : (fun p : LoopTwoSphere × LoopCircle =>
        c1LoopDerivative (L.map (Gamma.family p.1)) p.2 i) =
        (fun p => tangentMap (𝓡 3) (𝓡 3) f
          (c1LoopDerivative (Gamma.family p.1) p.2 i)) := by
      funext p
      rw [m59LoopPostcomposition_eq hf L]
      exact m59PostcomposeLoop_derivative f hf (Gamma.family p.1) p.2 i
    rw [heq]
    exact (hf.continuous_tangentMap (by simp)).comp (Gamma.derivative_continuous i)
  null_homotopic := fun c => by
    obtain ⟨extension, hcontinuous, hboundary⟩ := Gamma.null_homotopic c
    refine ⟨f ∘ extension, f.continuous.comp hcontinuous, ?_⟩
    intro z
    exact (congrArg f (hboundary z)).trans (m59LoopPostcomposition_apply L (Gamma.family c) z).symm
  joint_extension := by
    obtain ⟨extension, hcontinuous, hboundary, hregular⟩ := Gamma.joint_extension
    refine ⟨f ∘ extension, f.continuous.comp_continuousOn hcontinuous, ?_, ?_⟩
    · intro c z
      exact (congrArg f (hboundary c z)).trans
        (m59LoopPostcomposition_apply L (Gamma.family c) z).symm
    · intro c
      exact (hf.of_le (by simp)).comp_contMDiffOn (hregular c)

theorem m59_regular_postcomposition (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (L : M59LoopPostcomposition f) (Gamma : FreeTwoSphereFamily (M := M)) :
    ∃ Delta : FreeTwoSphereFamily (M := N),
      (∀ c, Delta.family c = L.map (Gamma.family c)) ∧
      Delta.class_certificate.sphere_parameter = Gamma.class_certificate.sphere_parameter ∧
      familySigmaClass Delta =
        ⟨f Gamma.basepoint, surgeryHomotopyMap (n := 2) L.map
          (L.maps_constant Gamma.basepoint) Gamma.homotopy_class⟩ :=
  ⟨m59PostcomposeFamily f hf L Gamma, fun _ => rfl, rfl, rfl⟩

end PoincareConjecture
