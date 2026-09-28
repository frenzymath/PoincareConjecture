import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RadialFamilies
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.NullLoopHomotopy
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.SphereDescent

set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m59GenLoop_null (n : Nat) [Nonempty (Fin n)] (x : M)
    (g : GenLoop (Fin n) (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (z : Fin n → I) : IsNullHomotopicLoop (g z) := by
  let zero : Fin n → I := fun _ => 0
  have hzero : zero ∈ Cube.boundary (Fin n) :=
    ⟨Classical.choice inferInstance, Or.inl rfl⟩
  let : PathConnectedSpace I :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  let p := (PathConnectedSpace.somePath z zero).map g.val.continuous
  apply m59NullLoop_of_path p
  rw [g.property zero hzero]
  exact ⟨fun _ => x, continuous_const, fun _ => rfl⟩

theorem m59SphereMap_null_of_pole (q : M59SphereQuotient) (x : M)
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (hbase : F q.pole = constantC1Loop x) : ∀ c, IsNullHomotopicLoop (F c) := by
  let g : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x) :=
    ⟨F.comp q.map, fun z hz => (congrArg F (q.boundary_collapsed z hz)).trans hbase⟩
  intro c
  obtain ⟨z, rfl⟩ := q.surjective c
  exact m59GenLoop_null 2 x g z

theorem m59_regular_representatives (q : M59SphereQuotient) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    ∃ Gamma : FreeTwoSphereFamily (M := M),
      M59NormalizedAt q x Gamma ∧ familySigmaClass Gamma = ⟨x, alpha⟩ := by
  refine Quotient.inductionOn alpha ?_
  intro g
  let F := q.descend g
  have hbase : F q.pole = constantC1Loop x := q.descend_pole g
  have hnull : ∀ c, IsNullHomotopicLoop (F c) := by
    intro c
    obtain ⟨z, rfl⟩ := q.surjective c
    change IsNullHomotopicLoop (q.descend g (q.map z))
    rw [q.descend_map]
    exact m59GenLoop_null 2 x g z
  let Gamma := m59RadialSphereFamily q x F hbase hnull
  refine ⟨Gamma, m59RadialSphereFamily_normalized q x F hbase hnull, ?_⟩
  have hcube :
      (⟨Gamma.class_certificate.cube_representative, Gamma.class_certificate.boundary_const⟩ :
        GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x)) =
      surgeryMappedGenLoop m59RadialLoopMap (m59RadialLoop_constant x) g := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    exact congrArg m59RadialLoop (q.descend_map g z)
  have hclass : Gamma.homotopy_class = Quotient.mk' g := by
    exact Gamma.class_certificate.class_eq.trans
      ((congrArg Quotient.mk' hcube).trans
        (Quotient.sound (m59RadialGenLoop_homotopic 2 x g).symm))
  exact congrArg (Sigma.mk x) hclass

end PoincareConjecture
