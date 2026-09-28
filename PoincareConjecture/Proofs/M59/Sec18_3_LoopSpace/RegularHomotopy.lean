import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.NormalizedCubes
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RegularRepresentatives











set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem m59_regular_homotopy_of_class_eq (q : M59SphereQuotient) (x : M)
    (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : M59NormalizedAt q x Gamma) (hDelta : M59NormalizedAt q x Delta)
    (hclass : familySigmaClass Gamma = familySigmaClass Delta) :
    FreeTwoSphereHomotopic Gamma Delta := by
  classical
  obtain ⟨H, hH⟩ := m59SphereHomotopy_of_class_eq q x Gamma Delta hGamma hDelta hclass
  let G (t : I) := m59RadialSphereFamily q x (H.curry t) (hH t)
    (m59SphereMap_null_of_pole q x (H.curry t) (hH t))
  let J (t : I) := if t = 0 then Gamma else if t = 1 then Delta else G t
  have hvalues (t : I) (c : LoopTwoSphere) (z : LoopCircle) :
      (J t).family c z = H (t, c) z := by
    dsimp only [J]
    split_ifs with h0 h1
    · subst t
      rw [H.apply_zero]
      rfl
    · subst t
      rw [H.apply_one]
      rfl
    · exact m59RadialLoop_apply (H (t, c)) z
  have htangents (t : I) (c : LoopTwoSphere) (z : LoopCircle) :
      c1LoopTangent ((J t).family c) z = c1LoopTangent (H (t, c)) z := by
    dsimp only [J]
    split_ifs with h0 h1
    · subst t
      rw [H.apply_zero]
      rfl
    · subst t
      rw [H.apply_one]
      rfl
    · exact m59RadialLoop_tangent (H (t, c)) z
  refine ⟨J, hGamma.1.trans hDelta.1.symm, hclass, ?_, ?_, ?_, ?_⟩
  · intro t
    dsimp only [J]
    split_ifs
    · rfl
    · exact hDelta.1.trans hGamma.1.symm
    · exact hGamma.1.symm
  · exact continuous_of_loop_firstJet_eq H.continuous
      (fun p => hvalues p.1 p.2) (fun p => htangents p.1 p.2)
  · simp [J]
  · simp [J]

end PoincareConjecture
