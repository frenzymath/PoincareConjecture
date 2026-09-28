import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedCollaredPLFilling
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ProtectedDiskFrontierPolygons

set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1

theorem PLDomain.exists_protected_collared_polygon_filling
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hF : IsCompact F)
    (hne : F.Nonempty) (hcut : Y ∩ frontier N = F)
    (gamma : C(Q, F)) (f : C(D, Y))
    (hf : ∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (gamma u : X)) :
    ∃ (g : V2 → X) (S : Set (Set V2)) (A B : C(I × Q, Y)),
      PolyhedralPLInCharts e g D ∧ MapsTo g D Y ∧
      S.Finite ∧
      (∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon V2 (n + 3),
        Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s) ∧
      S.PairwiseDisjoint id ∧ D ∩ g ⁻¹' F = ⋃ s ∈ S, s ∧
      (∀ s ∈ S, s ⊆ interior D) ∧
      (∀ u : Q, (A (0, u) : X) = (gamma u : X)) ∧
      (∀ u : Q, A (1, u) = B (0, u)) ∧
      (∀ u : Q, (B (1, u) : X) = g u) ∧
      (∀ (t : I) (u : Q), 0 < (t : ℝ) → (A (t, u) : X) ∈ interior N) ∧
      (∀ (t : I) (u : Q), (B (t, u) : X) ∈ interior N) ∧
      ∀ x ∈ Q, g x ∈ interior N := by
  classical
  let : Nonempty X := ⟨hne.choose⟩
  obtain ⟨q, d, A, T, hq, hqY, hqside, hA0, hA1, hAside, hT0, hT1, hTside⟩ :=
    hN.exists_protected_collared_PL_filling hY hF hne hcut gamma f hf
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodel
  have hfront : frontier K.space = Q := by
    rw [hKD, frontier_closedBall _ one_ne_zero]
  have hdim : Module.finrank ℝ V2 = 2 := by simp
  have hcv : Convex ℝ K.space := hKD.symm ▸ convex_closedBall (0 : V2) 1
  have hKinterior : (interior K.space).Nonempty := by
    rw [hKD]
    exact ⟨0, Metric.ball_subset_interior_closedBall (by simp)⟩
  have hnorm (u : Q) : (3 / 4 : ℝ) ≤ ‖(u : V2)‖ := by
    have hu : ‖(u : V2)‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using u.property
    rw [hu]
    norm_num
  have hboundary : ∀ x ∈ frontier K.space, q x ∉ F := by
    intro x hx hxF
    have hxQ := hfront.subset hx
    have hqint := hqside x (sphere_subset_closedBall hxQ) (hnorm ⟨x, hxQ⟩)
    exact ((hcut.symm ▸ hxF).2).2 hqint
  obtain ⟨G, g, S, hGY, hG0, hG1, hGfixed, hg, hS, hpoly, hdisjoint, hcover, hinterior⟩ :=
    hN.exists_protected_disk_frontier_polygons hY hcut K hK hdim hcv hKinterior q
      (hKD.symm ▸ hq) (hKD.symm ▸ hqY) hboundary
  have hgr (u : Q) : g u = q u := by
    let x : K.space := ⟨u, hKD.symm.subset (sphere_subset_closedBall u.property)⟩
    exact (hG1 x).symm.trans (hGfixed 1 x (hfront.symm.subset u.property))
  have hgY : MapsTo g D Y := by
    intro x hx
    have hy := hGY (1, ⟨x, hKD.symm.subset hx⟩)
    rw [hG1] at hy
    exact hy
  let B : C(I × Q, Y) := T.comp
    ⟨fun z => (z.1, ⟨z.2, sphere_subset_closedBall z.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  have hB1 (u : Q) : (B (1, u) : X) = g u :=
    (hT1 ⟨u, sphere_subset_closedBall u.property⟩).trans (hgr u).symm
  have hBside (t : I) (u : Q) : (B (t, u) : X) ∈ interior N :=
    hTside t ⟨u, sphere_subset_closedBall u.property⟩ (hnorm u)
  refine ⟨g, S, A, B, hKD ▸ hg, hgY, hS, hpoly, hdisjoint,
    hKD ▸ hcover, hKD ▸ hinterior, hA0, ?_, hB1, hAside, hBside, ?_⟩
  · intro u
    exact (hA1 u).trans (hT0 ⟨u, sphere_subset_closedBall u.property⟩).symm
  · intro x hx
    rw [← hB1 ⟨x, hx⟩]
    exact hBside 1 ⟨x, hx⟩

end PoincareConjecture.M76
