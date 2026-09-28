import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.PhaseLocalCollars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.RelativeCoverInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.ClopenIncompressibility
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.Injection









set_option autoImplicit false
open Set Geometry BrownCollar

namespace PoincareConjecture.M76

open HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

theorem marked_cover_sides_pi1_injective
    {X ι : Type*} [MetricSpace X] (e : ι → OpenPartialHomeomorph X V3)
    {R N M O A B : Set X}
    (hNR : N ⊆ R) (hMR : M ⊆ R) (hcover : N ∪ M = R)
    (hmeet : N ∩ M = A ∪ B) (hne : (A ∪ B).Nonempty)
    (hO : IsClosed O) (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hdata : ∀ T ∈ ({N, M} : Set (Set X)), IsCompact T ∧ ∃ _he : PLDomain e T,
      frontier T = (T ∩ O) ∪ (A ∪ B) ∧
      ∀ P ∈ ({A, B} : Set (Set X)),
        (∃ hPT : P ⊆ T, ∀ x : P, Function.Injective
          (FundamentalGroup.map (ContinuousMap.inclusion hPT) x)) ∧
        ∀ x ∈ P ∩ O,
          ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w v : V3) (G : OpenPartialHomeomorph X V3),
            psi.contLinear w = 1 ∧ psi.contLinear v = 0 ∧ lambda.contLinear v = 1 ∧
            x ∈ G.source ∧
            (∀ y ∈ G.source, y ∈ T ↔ 0 ≤ psi (G y)) ∧
            ∀ y ∈ G.source, y ∈ P ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    (∀ x : N, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hNR) x)) ∧
      ∀ x : M, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hMR) x) := by
  have hprepared (T : Set X) (hT : T ∈ ({N, M} : Set (Set X))) :
      IsCompact T ∧ ∃ hST : A ∪ B ⊆ T,
        (∀ x : ↥(A ∪ B),
          ∃ c : OpenPartialHomeomorph (↥(A ∪ B) × Ico (0 : ℝ) 1) T,
            collarBase x ∈ c.source ∧
              ∀ y, collarBase y ∈ c.source → c (collarBase y) = Set.inclusion hST y) ∧
        ∀ x : ↥(A ∪ B), Function.Injective
          (FundamentalGroup.map (ContinuousMap.inclusion hST) x) := by
    obtain ⟨hTc, he, hf, hp⟩ := hdata T hT
    obtain ⟨hST, hlocal⟩ := exists_phase_union_local_collars he (he.closed.inter hO)
      hA hB hf hdis (by
        intro P hP x hx
        obtain ⟨psi, lambda, w, v, G, hpw, hpv, hlv, hxG, hGN, hGP⟩ :=
          (hp P hP).2 x ⟨hx.1, hx.2.2⟩
        exact ⟨G, psi, lambda, w, v, hpw, hpv, hlv, hxG, hGN, hGP⟩)
    refine ⟨hTc, hST, hlocal, ?_⟩
    obtain ⟨hAT, hpiA⟩ := (hp A (Or.inl rfl)).1
    obtain ⟨hBT, hpiB⟩ := (hp B (Or.inr rfl)).1
    exact FundamentalGroup.inclusion_injective_of_disjoint_closed_union hA hB hdis rfl
      hST (fun _ => hpiA) (fun _ => hpiB)
  obtain ⟨hN, hSN, hcN, hpN⟩ := hprepared N (Or.inl rfl)
  obtain ⟨hM, hSM, hcM, hpM⟩ := hprepared M (Or.inr rfl)
  have hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ y, collarBase y ∈ c.source → c (collarBase y) = Set.inclusion inter_subset_left y := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hcN
  have hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧
          ∀ y, collarBase y ∈ c.source → c (collarBase y) = Set.inclusion inter_subset_right y := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hcM
  have hpiN : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x) := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hpN
  have hpiM : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) x) := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hpM
  exact relative_closed_cover_sides_pi1_injective hN hM hNR hMR hcover
    (hmeet.symm ▸ hne) hlocalN hlocalM hpiN hpiM

end PoincareConjecture.M76
