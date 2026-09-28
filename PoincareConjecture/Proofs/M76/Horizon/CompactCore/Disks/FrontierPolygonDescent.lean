import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.InnermostFrontierPolygonStep










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_essential_filling_or_frontier_avoidance
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hF : IsCompact F)
    (hFne : F.Nonempty) (hcut : Y ∩ frontier K = F)
    (g : V2 → X) (hg : ContinuousOn g D) (hgY : MapsTo g D Y)
    {S : Set (Set V2)} (hS : S.Finite)
    (hpoly : ∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon V2 (n + 3),
      Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s)
    (hdisj : S.PairwiseDisjoint id) (hcover : D ∩ g ⁻¹' F = ⋃ s ∈ S, s)
    (hsub : ∀ s ∈ S, s ⊆ interior D) :
    (∃ (f : C(D, Y)) (rim : C(Q, F)),
      (∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (rim u : X)) ∧
      (∀ x : D, (f x : X) ∈ F ↔ (x : V2) ∈ Q) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1) ∨
    ∃ g' : V2 → X, ContinuousOn g' D ∧ MapsTo g' D Y ∧
      EqOn g' g (frontier D) ∧ ∀ x ∈ D, g' x ∉ F := by
  classical
  induction hn : S.ncard using Nat.strong_induction_on generalizing S g with
  | h n ih =>
    by_cases hne : S.Nonempty
    · obtain ⟨s, f, rim, hs, hrim, hproper, hdelete⟩ :=
        hK.exists_innermost_frontier_polygon_step hY hF hFne hcut g hg hgY
          hS hne hpoly hdisj hcover hsub
      by_cases hnull : FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) = 1
      · have hrimnull : rim.Nullhomotopic :=
          Dehn.nullhomotopic_of_squareRimLoop rim (Path.Homotopic.Quotient.exact hnull)
        obtain ⟨g', hg', hg'Y, hfixed, hcover', hS', hdisj', hlt⟩ := hdelete hrimnull
        have hpoly' : ∀ t ∈ S \ {s}, ∃ n : ℕ, ∃ p : Polygon V2 (n + 3),
            Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = t :=
          fun t ht => hpoly t ht.1
        have hsub' : ∀ t ∈ S \ {s}, t ⊆ interior D := fun t ht => hsub t ht.1
        have hrec := ih (S \ {s}).ncard (hn ▸ hlt) g' hg' hg'Y
          hS' hpoly' hdisj' hcover' hsub' rfl
        rcases hrec with hgood | ⟨g'', hg'', hg''Y, hfixed', havoid⟩
        · exact Or.inl hgood
        · exact Or.inr ⟨g'', hg'', hg''Y, fun x hx =>
            (hfixed' hx).trans (hfixed hx), havoid⟩
      · exact Or.inl ⟨f, rim, hrim, hproper, hnull⟩
    · right
      refine ⟨g, hg, hgY, fun _ _ => rfl, ?_⟩
      intro x hx hxF
      have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp hne
      simpa only [hempty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty,
        mem_empty_iff_false] using hcover.subset ⟨hx, hxF⟩

end PoincareConjecture.M76
