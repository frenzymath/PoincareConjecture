import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SelectedHoleComplement

set_option autoImplicit false
open Set Metric Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "Cube" => closedBall (0 : V3) 1

theorem exists_marked_sphere_sides {S : Set V4}
    (e : S ≃ₜ frontier Cube) (he : e.IsFinitePL) (hSS : S ⊆ Sphere)
    (p : V4) (hp : p ∈ Sphere) (hpS : p ∉ S) :
    ∃ B : Set V4, IsFinitePLBallPair V3 B S ∧ B ⊆ Sphere ∧ p ∉ B ∧
      IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B \ S)) ∧
      IsFinitePLBallPair V3 (Sphere \ (B \ S)) S := by
  classical
  have hecopy := he
  obtain ⟨f₀, ⟨JS, hJS, hJSs, _⟩, _⟩ := hecopy
  have hSc : IsCompact S := hJSs ▸ JS.isCompact_space_of_finite hJS
  obtain ⟨J₀, _, hJ₀, hJ₀s, _, _⟩ := lower_ball.exists_finite_carrier_and_rim_complexes
  obtain ⟨J₁, _, hJ₁, hJ₁s, _, _⟩ := upper_ball.exists_finite_carrier_and_rim_complexes
  obtain ⟨J, hJ, hJs⟩ := J₀.exists_finite_triangulation_union J₁ hJ₀ hJ₁
  rw [hJ₀s, hJ₁s, lower_union_upper] at hJs
  obtain ⟨D, b, hD, hDS, hSD, hpD, hDopen⟩ :=
    J.exists_convex_frontier_disk_of_compact_with_open_interior hJ
      (isCompact_closedBall (0 : V4) 1) (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hJs
      (F := V3) (by simp) ⟨p, hp⟩ hSc hSS hpS
  obtain ⟨Q, f, g, hQs, hQt, hf, hg, hQf, hQg, hgm, hgf, hfg⟩ :=
    hD.exists_open_cube_interior_chart (ContinuousLinearEquiv.refl ℝ V3) hDS hDopen
  have hsource (x : V4) (hx : x ∈ S) : (⟨x, hSS hx⟩ : Sphere) ∈ Q.source := by
    rw [hQs]
    exact hSD hx
  have hfS : FinitePiecewiseAffineOn f S := by
    rw [← hJSs]
    exact hf.restrict JS hJS (hJSs.subset.trans (hSD.trans sdiff_subset))
  obtain ⟨j, hj, _⟩ := hfS.exists_homeomorph_image
    (hgf.injOn.mono (hSD.trans sdiff_subset))
  have himage : f '' S ⊆ interior Cube := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hQf ⟨x, hSS hx⟩, ← hQt]
    exact Q.map_source (hsource x hx)
  have hgcopy := hg
  obtain ⟨JC, hJC, hJCs, _⟩ := hgcopy
  obtain ⟨U, hU, _, hUf, hUC, hUB, _⟩ :=
    (hj.symm.trans he).hasAlexanderRegionBalls
      (isCompact_closedBall _ _) (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp) (by simp)
      (isCompact_closedBall _ _) (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ himage JC hJC hJCs
  let B := g '' closure U
  have hback : g '' (f '' S) = S := by
    rw [image_image]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change g (f x) ∈ S
      rwa [hgf ((hSD hx).1)]
    · intro x hx
      exact ⟨x, hx, hgf ((hSD hx).1)⟩
  have hball₀ : IsFinitePLBallPair P3 B S := by
    have hh := hUB.image_of_subset hg (hUC.trans interior_subset) hfg.injOn
    rwa [hback] at hh
  let coord : P3 ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨c, hc, hcb⟩ := hball₀.exists_cube_chart coord
  have hball : IsFinitePLBallPair V3 B S :=
    ⟨hball₀.1, Cube, isCompact_closedBall _ _, convex_closedBall _ _,
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩, c, hc, hcb⟩
  have hBD : B ⊆ D := image_subset_iff.mpr fun _ hx => hgm (interior_subset (hUC hx))
  have hpB : p ∉ B := fun hx => hpD (hBD hx)
  have hBS : B ⊆ Sphere := hBD.trans hDS
  have hpre : (Subtype.val : Sphere → V4) ⁻¹' (B \ S) = Q.symm '' U := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hxS⟩
      have hyU : y ∈ U := by
        by_contra hn
        have hyf : y ∈ frontier U := ⟨hy, by simpa only [hU.interior_eq] using hn⟩
        exact hxS (hyx ▸ hback.subset ⟨y, hUf.subset hyf, rfl⟩)
      exact ⟨y, hyU, Subtype.ext ((hQg y (interior_subset (hUC hy))).trans hyx)⟩
    · rintro ⟨y, hy, rfl⟩
      change (Q.symm y : V4) ∈ B \ S
      rw [hQg y (interior_subset (hUC (subset_closure hy)))]
      refine ⟨⟨y, subset_closure hy, rfl⟩, ?_⟩
      intro hgyS
      have hyS : y ∈ f '' S := ⟨g y, hgyS, hfg (interior_subset (hUC (subset_closure hy)))⟩
      exact (hUf.symm.subset hyS).2 (hU.interior_eq.symm ▸ hy)
  have hopen : IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B \ S)) := by
    rw [hpre]
    exact Q.symm.isOpen_image_of_subset_source hU
      (subset_closure.trans (hUC.trans hQt.symm.subset))
  exact ⟨B, hball, hBS, hpB, hopen, hball.selected_hole_complement hBS hopen⟩

end Set
