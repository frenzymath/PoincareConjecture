import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.FrontierPolygonDescent
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.EmptyFrontierPolygonFilling
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.OriginalFrontierCompressionAlternative
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedCollaredPolygonFilling
import PoincareConjecture.Proofs.M76.Wall.ProtectedOpenRegion

set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_essential_proper_filling_of_protected_filling
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hF : IsCompact F)
    (hFne : F.Nonempty) (hcut : Y ∩ frontier K = F)
    (gamma : C(Q, F)) (initial : C(D, Y))
    (hinitial : ∀ u : Q,
      (initial ⟨u, sphere_subset_closedBall u.property⟩ : X) = (gamma u : X))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ (f : C(D, Y)) (rim : C(Q, F)),
      (∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (rim u : X)) ∧
      (∀ x : D, (f x : X) ∈ F ↔ (x : V2) ∈ Q) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 := by
  obtain ⟨g, S, A, B, hg, hgY, hS, hpoly, hdisj, hcover, hsub,
    hA0, hAB, hB1, hAside, hBside, _⟩ :=
    hK.exists_protected_collared_polygon_filling hY hF hFne hcut gamma initial hinitial
  rcases hK.exists_essential_filling_or_frontier_avoidance hY hF hFne hcut
      g hg.continuousOn hgY hS hpoly hdisj hcover hsub with
      hproper | ⟨g', hg', hg'Y, hfixed, havoid⟩
  · exact hproper
  · let residual : C(D, Y) :=
      ⟨fun x => ⟨g' x, hg'Y x.property⟩, hg'.domRestrict.subtype_mk _⟩
    have hB1' (u : Q) : B (1, u) = residual ⟨u, sphere_subset_closedBall u.property⟩ := by
      apply Subtype.ext
      exact (hB1 u).trans (hfixed (by
        rw [frontier_closedBall _ one_ne_zero]
        exact u.property)).symm
    obtain ⟨f, hf, _, _, hproper⟩ :=
      hK.exists_proper_filling_of_empty_frontier_preimage hcut gamma residual A B
        hA0 hAB hB1' (fun x => havoid x x.property) hAside hBside
    exact ⟨f, gamma, hf, hproper, hessential⟩

theorem PLDomain.exists_new_frontier_spheres_or_essential_proper_fillings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N F R C : Set X}
    (he : PLDomain e N) (hN : IsCompact N)
    (hF : IsCompact F) (hFne : F.Nonempty) (hFR : F ⊆ R)
    (hBF : Disjoint (frontier R) F) (hfront : frontier N = frontier R ∪ F)
    (hC : IsCompact C) (hBC : frontier R ⊆ C)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' N))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' N) =
      (Subtype.val : R → X) ⁻¹' F)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    ∃ (n : ℕ) (S : Fin n → Set X), 0 < n ∧ (⋃ i, S i) = F ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        ∀ x ∈ S i, connectedComponentIn F x = S i) ∧
      ∀ i, Nonempty (ChartwisePLSphere e (S i)) ∨
        ∃ (f : C(D, (R \ C : Set X))) (rim : C(Q, F)),
          (∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (rim u : X)) ∧
          (∀ x : D, (f x : X) ∈ F ↔ (x : V2) ∈ Q) ∧
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 := by
  obtain ⟨hY, hFY, hcut⟩ :=
    Set.protected_open_cut_region hC.isClosed hBC hFR hprotect hrel hfront
  have hNne : N.Nonempty := by
    obtain ⟨x, hx⟩ := hFne
    refine ⟨x, he.closed.frontier_subset ?_⟩
    rw [hfront]
    exact Or.inr hx
  obtain ⟨n, S, hn, hcover, hdisj, hcomponents, halt⟩ :=
    he.exists_new_frontier_spheres_or_protected_fillings hN hNne isClosed_frontier
      hF.isClosed hBF hfront hFne hFY hloops
  refine ⟨n, S, hn, hcover, hdisj, hcomponents, ?_⟩
  intro i
  rcases halt i with hsphere | ⟨_, gamma, initial, _, _, _, _, hessential, hinitial⟩
  · exact Or.inl hsphere
  · exact Or.inr (he.exists_essential_proper_filling_of_protected_filling
      hY hF hFne hcut gamma initial hinitial hessential)

end PoincareConjecture.M76
