import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SelectedHoleRegionRecognition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.MarkedPuncturedDoubleSphere
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FinitePLBallInteriorChart
import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereLargeDisks
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences











set_option autoImplicit false

open Set Metric Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)




theorem IsFinitePLBallPair.selected_hole_complement
    {a r : Set V4} (ha : IsFinitePLBallPair V3 a r) (haS : a ⊆ sphere)
    (hopen : IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a \ r))) :
    IsFinitePLBallPair V3 (sphere \ (a \ r)) r := by
  classical
  let A : Set sphere := (Subtype.val : sphere → V4) ⁻¹' (a \ r)
  let R : Set sphere := (Subtype.val : sphere → V4) ⁻¹' r
  let K : Set V4 := sphere \ (a \ r)
  have hSc : IsCompact sphere := (isCompact_closedBall (0 : V4) 1).of_isClosed_subset
    isClosed_frontier isClosed_closedBall.frontier_subset
  let : CompactSpace sphere := isCompact_iff_compactSpace.mp hSc
  obtain ⟨p, hpa, hpr⟩ := ha.isConnected_sdiff.nonempty
  let pole : sphere := ⟨p, haS hpa⟩
  have hAc : IsConnected A := by
    refine ⟨⟨pole, hpa, hpr⟩, ?_⟩
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset (by simpa using sdiff_subset.trans haS)]
    exact ha.isConnected_sdiff.isPreconnected
  have hRA : R ⊆ Aᶜ := fun _ hr hA => hA.2 hr
  have hAf : frontier A ⊆ R := by
    intro x hx
    have hcl : closure A ⊆ (Subtype.val : sphere → V4) ⁻¹' a :=
      closure_minimal (preimage_mono sdiff_subset)
        (ha.isCompact.isClosed.preimage continuous_subtype_val)
    have hxa := hcl hx.1
    by_contra hxr
    exact hx.2 (hopen.interior_eq.symm ▸ (show x ∈ A from ⟨hxa, hxr⟩))
  have hKimage : (Subtype.val : sphere → V4) '' Aᶜ = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hKc : IsCompact K := hKimage ▸ hopen.isClosed_compl.isCompact.image
    continuous_subtype_val
  have hrK : r ⊆ K := fun x hx => ⟨haS (ha.1 hx), fun h => h.2 hx⟩
  obtain ⟨J₀, _, hJ₀, hJ₀s, _, _⟩ := lower_ball.exists_finite_carrier_and_rim_complexes
  obtain ⟨J₁, _, hJ₁, hJ₁s, _, _⟩ := upper_ball.exists_finite_carrier_and_rim_complexes
  obtain ⟨J, hJ, hJs⟩ := J₀.exists_finite_triangulation_union J₁ hJ₀ hJ₁
  rw [hJ₀s, hJ₁s, lower_union_upper] at hJs
  obtain ⟨D, b, hD, hDS, hKD, hpD, hDopen⟩ :=
    J.exists_convex_frontier_disk_of_compact_with_open_interior hJ
      (isCompact_closedBall (0 : V4) 1) (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hJs
      (F := V3) (by simp) pole hKc sdiff_subset (by
        intro hpK
        exact hpK.2 ⟨hpa, hpr⟩)
  obtain ⟨Q, f, g, hQs, hQt, hf, hg, hQf, hQg, hgm, hgf, hfg⟩ :=
    hD.exists_open_cube_interior_chart (ContinuousLinearEquiv.refl ℝ V3) hDS hDopen
  have hKsource : Aᶜ ⊆ Q.source := by
    intro x hx
    rw [hQs]
    exact hKD ⟨x.property, hx⟩
  have hRsource : R ⊆ Q.source := hRA.trans hKsource
  have hpQ : pole ∉ Q.source := by
    rw [hQs]
    exact fun h => hpD h.1
  have hRimage : Q '' R = f '' r := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hQf x).symm⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, haS (ha.1 hx)⟩, hx, hQf _⟩
  have hrD : r ⊆ D := hrK.trans (hKD.trans sdiff_subset)
  have hfrC : f '' r ⊆ interior (closedBall (0 : V3) 1) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hQf ⟨x, haS (ha.1 hx)⟩, ← hQt]
    exact Q.map_source (hRsource hx)
  obtain ⟨ea, hea, hear⟩ := ha.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨_, Jr, _, _, hJr, hJrs⟩ := ha.exists_finite_carrier_and_rim_complexes
  let er := ea.restrictSubsets ha.1 isClosed_closedBall.frontier_subset hear
  have her : er.IsFinitePL := hea.restrictSubsets ha.1
    isClosed_closedBall.frontier_subset hear Jr hJr hJrs
  have hfr : FinitePiecewiseAffineOn f r := by
    rw [← hJrs]
    exact hf.restrict Jr hJr (hJrs.subset.trans hrD)
  obtain ⟨j, hj, _⟩ := hfr.exists_homeomorph_image (hgf.injOn.mono hrD)
  have hgcopy := hg
  obtain ⟨JC, hJC, hJCs, _⟩ := hgcopy
  have hregions := (hj.symm.trans her).hasAlexanderRegionBalls
    (isCompact_closedBall (0 : V3) 1) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp) (by simp)
    (isCompact_closedBall (0 : V3) 1) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hfrC JC hJC hJCs
  obtain ⟨U, hU, _, hUf, hUC, hUB, hUE⟩ := hregions
  have hEq : Q '' Aᶜ = closure U :=
    Q.image_complement_eq_alexander_bounded_side hAc hAf hRA
      hopen.isClosed_compl.isCompact hKsource hQt pole ⟨hpa, hpr⟩ hpQ hU
      (hRimage.symm ▸ hUf) (hQt.symm ▸ hUC) hUB.isCompact (hRimage.symm ▸ hUE)
  have hback : g '' closure U = K := by
    rw [← hEq, image_image, ← hKimage]
    apply image_congr
    intro x hx
    rw [hQf]
    exact hgf ((hKD ⟨x.property, hx⟩).1)
  have hrback : g '' (f '' r) = r := by
    rw [image_image]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change g (f x) ∈ r
      rwa [hgf (hrD hx)]
    · intro x hx
      exact ⟨x, hx, hgf (hrD hx)⟩
  have hresult := hUB.image_of_subset hg (hUC.trans interior_subset) hfg.injOn
  rw [hback, hrback] at hresult
  let coord : P3 ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨e, he, heb⟩ := hresult.exists_cube_chart coord
  exact ⟨hresult.1, closedBall (0 : V3) 1, isCompact_closedBall _ _, convex_closedBall _ _,
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩, e, he, heb⟩

end Set
