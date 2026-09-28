import PoincareConjecture.Proofs.M76.Wall.OriginalNewFrontierModels
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Loops.OriginalComponentAlternative
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedFrontierFilling











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1

theorem PLDomain.exists_new_frontier_spheres_or_protected_fillings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B F R C : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hFne : F.Nonempty)
    (hFU : F ⊆ R \ C)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    ∃ (n : ℕ) (S : Fin n → Set X), 0 < n ∧ (⋃ i, S i) = F ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        ∀ x ∈ S i, connectedComponentIn F x = S i) ∧
      ∀ i, Nonempty (ChartwisePLSphere e (S i)) ∨
        ∃ (b : V2 → X) (gamma : C(Q, F)) (f : C(D, (R \ C : Set X))),
          (∀ x : Q, (gamma x : X) = b x) ∧
          (∀ x : Q, (gamma x : X) ∈ S i) ∧
          Topology.IsEmbedding gamma ∧ PolyhedralPLInCharts e b Q ∧
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 ∧
          (∀ x : Q, (f ⟨x, sphere_subset_closedBall x.property⟩ : X) = (gamma x : X)) := by
  classical
  obtain ⟨s, phi, K, A, H, g, HB, n, pick, S, _, _, hK, hAK, _, _, _, _, _,
    _, hg, hgPL, _, _, _, _, hpure, hcofaces, hlinks, hn, _, hunion, hdisjoint,
    hcomponents, _⟩ := he.exists_new_frontier_component_models hN hNne hB hF hBF
      hfront hFne
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro x hx y hy hxy
    have hinv : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hinv)
  refine ⟨n, S, hn, hunion, hdisjoint, ?_, ?_⟩
  · intro i
    obtain ⟨hc, hn, hs, heq, _⟩ := hcomponents i
    exact ⟨hc, hn, hs, heq⟩
  · intro i
    obtain ⟨_, _, hSF, hcomponent, _, HC, hHC⟩ := hcomponents i
    rcases original_frontier_component_sphere_or_essential_rim e K A hK hAK
        (pick i) hpure hcofaces hlinks hSF hcomponent HC (fun z => (g z : X))
        hHC hgPL hgi with hsphere | hrim
    · exact Or.inl hsphere
    · obtain ⟨m, P, a, d, gamma, _, _, _, _, _, _, _, _, hgamma, hgammaS,
        hemb, hPL, hnontrivial⟩ := hrim
      obtain ⟨f, hf⟩ := exists_prescribed_frontier_filling_in_protected_region
        hFU hloops gamma
      exact Or.inr ⟨(fun z => (g z : X)) ∘ d, gamma, f, hgamma, hgammaS,
        hemb, hPL, hnontrivial, hf⟩

end PoincareConjecture.M76
