import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}

structure M64FiniteNetPackage
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (mu : ℝ) where
  node_count : ℕ
  nodes : Fin node_count → LoopTwoSphere
  circumference_cutoff : ℝ
  cutoff_positive : 0 < circumference_cutoff
  covers : ∀ z : LoopTwoSphere, ∃ i : Fin node_count,
    ∀ circumference (h : 0 < circumference), circumference < circumference_cutoff →
      ∃ A : M64Annulus ((G.product circumference h).flow.metric a)
        (m63CanonicalRamp (G.product circumference h) (periodicFreeLoop (Gamma z)))
        (m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (Gamma (nodes i)))), A.area < mu

def M64FiniteNetPackage.toNet
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {mu : ℝ} (P : M64FiniteNetPackage (G := G) Gamma mu) :
    M64FamilyAnnulusNet G Gamma mu :=
  { node_count := P.node_count
    nodes := P.nodes
    circumference_cutoff := P.circumference_cutoff
    cutoff_positive := P.cutoff_positive
    covers := P.covers }

theorem m64FamilyAnnulusNet_of_package
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {mu : ℝ} (P : M64FiniteNetPackage (G := G) Gamma mu) :
    Nonempty (M64FamilyAnnulusNet G Gamma mu) :=
  ⟨P.toNet⟩

theorem m64FamilyAnnulusNets_of_package_supplier
    (hpackage : ∀ Gamma : ContinuousMap LoopTwoSphere
      (C1FreeLoopSpace (M := M)), ∀ mu : ℝ, 0 < mu →
      Nonempty (M64FiniteNetPackage (G := G) Gamma mu)) :
    M64FamilyAnnulusNets G := by
  intro Gamma mu hmu
  obtain ⟨P⟩ := hpackage Gamma mu hmu
  exact m64FamilyAnnulusNet_of_package P

end PoincareConjecture
