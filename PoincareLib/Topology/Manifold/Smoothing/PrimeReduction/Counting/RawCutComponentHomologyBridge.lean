import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.RawCutComponentHomology
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.ComponentHomeomorphTransport
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.RawCutComponentHomotopy

/-! # Homology transport from the finite model to a literal cut component -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits
open scoped Topology
universe u v
namespace PoincareMT.M76

theorem exists_raw_cut_component_homology_retract_of_homeomorph
    {E : Type u} [TopologicalSpace E]
    {U R Q : Set E} {κ : Type v} [Finite κ]
    {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    {O S : κ → Set E}
    (T : U ≃ₜ (Set.diff R (⋃ i, S i)))
    (x : U)
    {M : ModuleCat.{u} (ZMod 2)}
    (i₀ : M ⟶ (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn U (x : E)))).homology M 1)
    (r₀ : (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn U (x : E)))).homology M 1 ⟶ M)
    (hi₀ : i₀ ≫ r₀ = 𝟙 M)
    (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = Set.diff R (⋃ i, O i)) (hcQ : IsClosed Q)
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀ i z, (W i z : E) ∈ O i ↔
      (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀ i z, (W i z : E) ∈ S i ↔ (z.2 : ℝ) = 1 / 2)
    (hSC : ∀ i, S i ⊆ closure (O i)) :
    ∃ q : Q, (q : E) ∈ connectedComponentIn (Set.diff R (⋃ i, S i)) (T x : E) ∧
      connectedComponentIn Q q =
        connectedComponentIn (Set.diff R (⋃ i, S i)) (T x : E) ∩ Q ∧
      ∃ (i : M ⟶ (TopCat.toSSet.obj (TopCat.of
          (connectedComponentIn Q q))).homology M 1)
        (r : (TopCat.toSSet.obj (TopCat.of
          (connectedComponentIn Q q))).homology M 1 ⟶ M),
        i ≫ r = 𝟙 M := by
  obtain ⟨i₁,r₁,hi₁⟩ :=
    module_homology_retract_of_component_homeomorph T x i₀ r₀ hi₀
  obtain ⟨q,hqx,hcomponent,e,he⟩ := exists_raw_cut_component_homotopyEquiv
    R Q O S W hQ hcQ hCR hdis hO hS hSC (T x)
  obtain ⟨i₂,r₂,hi₂⟩ := CutGraph.module_homology_retract_of_homotopyEquiv
    M e 1 i₁ r₁ hi₁
  exact ⟨q,hqx,hcomponent,i₂,r₂,hi₂⟩

end PoincareMT.M76
