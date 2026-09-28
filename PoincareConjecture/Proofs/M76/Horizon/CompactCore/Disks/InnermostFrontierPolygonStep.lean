import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.CollaredNullCircleDeletion
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.ParametrizedDiskCollar
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.ProtectedPolygonNeighborhood
import PoincareConjecture.Proofs.M76.Wall.ProtectedFrontierBicollar

set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_innermost_frontier_polygon_step
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hF : IsCompact F)
    (hFne : F.Nonempty) (hcut : Y ∩ frontier K = F)
    (g : V2 → X) (hg : ContinuousOn g D) (hgY : MapsTo g D Y)
    {S : Set (Set V2)} (hS : S.Finite) (hne : S.Nonempty)
    (hpoly : ∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon V2 (n + 3),
      Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s)
    (hdisj : S.PairwiseDisjoint id) (hcover : D ∩ g ⁻¹' F = ⋃ s ∈ S, s)
    (hsub : ∀ s ∈ S, s ⊆ interior D) :
    ∃ (s : Set V2) (f : C(D, Y)) (rim : C(Q, F)), s ∈ S ∧
      (∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (rim u : X)) ∧
      (∀ x : D, (f x : X) ∈ F ↔ (x : V2) ∈ Q) ∧
      (rim.Nullhomotopic → ∃ g' : V2 → X,
        ContinuousOn g' D ∧ MapsTo g' D Y ∧ EqOn g' g (frontier D) ∧
        D ∩ g' ⁻¹' F = ⋃ t ∈ S \ {s}, t ∧
        (S \ {s}).Finite ∧ (S \ {s}).PairwiseDisjoint id ∧
        (S \ {s}).ncard < S.ncard) := by
  obtain ⟨s, B, a, d, hs, hball, hBD, _, _, hd, hval, _, himage,
    _, hrim, hinter, _, hcollar⟩ :=
    exists_innermost_frontier_polygon_disk_with_collar hS hne hpoly hdisj hsub
  have hfrontD : frontier D = Q := frontier_closedBall _ one_ne_zero
  rw [hfrontD] at hrim
  have harim (x : D) : (a x : V2) ∈ s ↔ (x : V2) ∈ Q := by
    rw [← hval]
    exact hrim x
  have haD (x : D) : (a x : V2) ∈ D := interior_subset (hBD (a x).property)
  have hga : Continuous (fun x : D => g (a x)) :=
    hg.comp_continuous (continuous_subtype_val.comp a.continuous) haD
  have hproper (x : D) : g (a x) ∈ F ↔ (x : V2) ∈ Q := by
    constructor
    · intro hx
      exact (harim x).mp (hinter.subset ⟨(a x).property, hcover.subset ⟨haD x, hx⟩⟩)
    · intro hx
      exact (hcover.superset (hinter.superset ((harim x).mpr hx)).2).2
  let f : C(D, Y) := ⟨fun x => ⟨g (a x), hgY (haD x)⟩, hga.subtype_mk _⟩
  let rim : C(Q, F) :=
    ⟨fun u => ⟨g (a ⟨u, sphere_subset_closedBall u.property⟩),
      (hproper ⟨u, sphere_subset_closedBall u.property⟩).mpr u.property⟩,
      (hga.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  refine ⟨s, f, rim, hs, fun _ => rfl, hproper, ?_⟩
  intro hnull
  obtain ⟨U, hU, hFU, hUY, G, hGbase, _, hGzero⟩ :=
    hK.exists_protected_frontier_bicollar hY hF hFne hcut
  have hsU : MapsTo g s U := by
    intro x hx
    exact hFU (hcover.superset (mem_iUnion₂.mpr ⟨s, hs, hx⟩)).2
  have hclosed : ∀ t ∈ S, IsClosed t := by
    intro t ht
    obtain ⟨n, p, _, _, hpb⟩ := hpoly t ht
    exact hpb ▸ p.isCompact_boundary.isClosed
  obtain ⟨W, hW, hsW, hWD, hgWU, hWfamily⟩ :=
    exists_protected_polygon_neighborhood hg hU (hsub s hs) hsU hS hs hclosed hdisj
  obtain ⟨k, hk, hkbase, hkW, hkout, hcompact, _, hfront⟩ := hcollar W hW hsW
  obtain ⟨c, _, hc, hcbase, hrange, hlevel, hcout, _, _⟩ :=
    exists_parametrized_disk_collar a hball.1 harim k hk hkbase hkout
  have hcW (z : Q × I) : c z ∈ W := by
    have hz : c z ∈ range k := hrange.subset (mem_range_self z)
    obtain ⟨w, hw⟩ := hz
    exact hw ▸ hkW w
  have hED : B ∪ range c ⊆ interior D := by
    rintro x (hx | ⟨z, rfl⟩)
    · exact hBD hx
    · exact hWD (hcW z)
  have hEclosed : IsClosed (B ∪ range c) := by
    rw [hrange]
    exact hcompact.isClosed
  have hEfront : frontier (B ∪ range c) ⊆ range (fun u : Q => c (u, 1)) := by
    rw [hrange, hlevel]
    exact hfront
  have hEfamily : (B ∪ range c) ∩ (⋃ t ∈ S, t) = s :=
    collar_enlargement_inter_family hinter hWfamily subset_union_left (by
      rintro x (hx | ⟨z, rfl⟩)
      · exact Or.inl hx
      · exact Or.inr (hcW z))
  obtain ⟨g', hg', hg'Y, _, hg'front, _, hpreimage, hfinite, hpair, _, hdecrease⟩ :=
    exists_collared_null_circle_deletion hUY G hGbase hGzero hg hgY a c hc.injective
      hcbase hcout hEclosed hED hEfront (fun z => hgWU (hcW z)) hS hdisj hs
      hball.1 hEfamily hcover rim (fun _ => rfl) hnull
  exact ⟨g', hg', hg'Y, hg'front, hpreimage, hfinite, hpair, hdecrease⟩

end PoincareConjecture.M76
