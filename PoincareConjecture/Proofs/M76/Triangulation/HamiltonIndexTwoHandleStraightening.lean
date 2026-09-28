import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerCappedAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardCollarIdentity
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoProtectedPlacement
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedHandleComparison
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedCoreConstruction
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedAtlasCorrection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonFiniteHandleCoordinates

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "W" => ((Fin 2 ⊕ Fin 1) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 2 ↪ Fin 2 ⊕ Fin 1)
local notation "D" => coordinateCylinder J
local notation "pi" => latticeCoordinateProjection (Fin 2) (Fin 1) L

theorem exists_hamilton_indexTwo_handle_straightening
    (h : OpenPartialHomeomorph (V2 × V1) V3)
    (hsource : closedBall (0 : V2) 1 ×ˢ (univ : Set V1) ⊆ h.source)
    {N0 : Set (V2 × V1)} (hN0 : IsOpen N0)
    (hboundary0 : sphere (0 : V2) 1 ×ˢ (univ : Set V1) ⊆ N0)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N0))
    (wall : ∀ (U : TopologicalSpace.Opens X)
      (charts : Set (OpenPartialHomeomorph U V3)),
      HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3)))
    (brown : HasBrownLocallyFlatSphereBalls)
    (dehn : ∀ charts : Set (OpenPartialHomeomorph X V3),
      HasHamiltonProtectedDehnDisks L (fun c : charts => (c : OpenPartialHomeomorph X V3)))
    (prime : ∀ charts : Set (OpenPartialHomeomorph X V3),
      HasHamiltonProtectedIrreducibleReplacement (Fin 2) (Fin 1) L
        (fun c : charts => (c : OpenPartialHomeomorph X V3)))
    (approximation : ∀ (charts : Set (OpenPartialHomeomorph X V3))
      (d : (V2 × V1) → OpenPartialHomeomorph X V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph X V3)) d R)
    (rigidity : ∀ (charts : Set (OpenPartialHomeomorph X V3))
      (d : (V2 × V1) → OpenPartialHomeomorph X V3),
      HasHamiltonRelativeTorusRigidity (Fin 2) (Fin 1) L
        (fun c : charts => (c : OpenPartialHomeomorph X V3)) d) :
    ∃ B : W ≃ₜ W,
      FinitePiecewiseAffineOn
        ((fun x : W => h ((fun i => x (Sum.inl i)), fun i => x (Sum.inr i))) ∘ B)
        (closedBall (0 : W) 1) ∧
      Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id W) ⟨B, B.continuous⟩
        (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
          ∀ x ∈ Dᶜ ∪ frontier D, f x = x)) := by
  classical
  obtain ⟨I⟩ := exists_lower_lattice_immersion_one
  obtain ⟨r0, _, hr01, d, charts, hd, he, ⟨retained⟩, hstandard⟩ :=
    I.exists_capped_original_PL_domain (by simp) h hsource hN0 hboundary0 hPL wall brown
  let e : charts → OpenPartialHomeomorph X V3 := fun i => i
  have hfront0 : frontier (closedBall (0 : V2) 1 ×ˢ (univ : Set V1)) ⊆ N0 := by
    simpa only [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] using hboundary0
  obtain ⟨T, ⟨region⟩⟩ := dehn charts he h hsource N0 hN0 hfront0 hPL ⟨retained⟩
  obtain ⟨ball⟩ := region.markedProtectedBall he h retained (Or.inr (by simp))
  obtain ⟨geometry⟩ := retained.exists_indexTwo_dehn_geometry L e T region
  let O : Set X := {x | r0 < ‖x.1‖}
  have hO : IsOpen O := isOpen_lt continuous_const continuous_fst.norm
  have hboundary := hd.chartwisePLOn_identity_of_restricted_charts
    (Fin 2) (Fin 1) L d charts he hO hstandard
  have hBO : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      (Subtype.val : R → X) ⁻¹' O := by
    intro x hx
    have hn : ‖(x : X).1‖ = 1 := by
      have hf : frontier R = sphere (0 : V2) 1 ×ˢ
          (univ : Set (V1 ⧸ (hamiltonLowerPeriodLattice (Fin 1)).toAddSubgroup)) := by
        simp only [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
      exact mem_sphere_zero_iff_norm.mp (hf.subset hx).1
    change r0 < ‖(x : X).1‖
    rwa [hn]
  obtain ⟨replacement, N, _, hPN, _, hforward, hback, g, hgPL,
    G, hG, _, _, _, _, p, hps, _, _, hpwide, hpPL, hpiPL, A, hA, ⟨HA⟩⟩ :=
    exists_hamilton_protected_handle_comparison (Fin 2) (Fin 1) L
      e d (by simp) (by simp) he hd (prime charts)
      (fun replacement => approximation replacement d)
      (fun replacement => rigidity replacement d) region.region ⟨ball⟩
      ((Subtype.val : R → X) ⁻¹' O) hBO hboundary
      geometry.radius_gt_one geometry.radius_lt_two
  let e' : replacement → OpenPartialHomeomorph X V3 := fun i => i
  have hPfix : EqOn p id geometry.Psum := fun x hx =>
    hpwide x (geometry.in_cylinder hx) (geometry.norm_le x hx)
  have hPiN (x : W) (hx : x ∈ geometry.Psum) : pi x ∈ N := by
    apply hPN
    left
    rw [← geometry.regionProjection_eq ⟨x, hx⟩]
    exact (geometry.regionProjection ⟨x, hx⟩).property
  have hAout (x : W) (hx : 2 ≤ ‖x‖) : A x = x := by
    have hfix := (HA.prop 1).2.1 x hx
    change HA (1, x) = x at hfix
    rwa [HA.apply_one] at hfix
  have hArel (x : W) (hx : x ∈ Dᶜ ∪ frontier D) : A x = x := by
    have hfix := (HA.prop 1).2.2 x hx
    change HA (1, x) = x at hfix
    rwa [HA.apply_one] at hfix
  obtain ⟨Q, hQPL, hQout, hQrel, hplace⟩ :=
    geometry.exists_protected_cover_placement ball e' d hd N hforward
      g hgPL G hG p hps hpPL A hA hPfix hPiN hAout hArel
  let original : W → V3 := fun x => h ((fun i => x (Sum.inl i)), fun i => x (Sum.inr i))
  have hC2 (x : W) (hx : x ∈ geometry.Psum) :
      ((fun i => x (Sum.inl i)), fun i => x (Sum.inr i)) ∈
        closedBall (0 : V2) 1 ×ˢ closedBall (0 : V1) 2 := by
    rw [geometry.Psum_eq] at hx
    exact hx.1
  have hchart (x : W) (hx : x ∈ geometry.Psum) : pi x ∈ (e retained.index).source :=
    retained.contains _ (hC2 x hx)
  have hformula (x : W) (hx : x ∈ geometry.Psum) :
      original x = (ContinuousAffineMap.id ℝ V3) (e retained.index (pi x)) :=
    (retained.formula _ (hC2 x hx)).symm
  obtain ⟨data, hdata⟩ := exists_hamiltonProtectedCoreData_of_fixed_region_marked
    original e d hd p hps hpiPL A G hA geometry.Psum hPfix geometry.in_cylinder
      retained.index (ContinuousAffineMap.id ℝ V3) hchart hformula
      Q hQPL hQout hQrel hplace
  obtain ⟨B, _, hB, hBH⟩ := lowerHandleStraightening_of_protected_atlas_comparison
    original e e' d ((Subtype.val : R → X) ⁻¹' N) hback g hgPL G hG
      p hps A hA hAout hArel data (by
        intro x hx
        change pi x ∈ N
        apply hPiN x
        rwa [← hdata])
  exact ⟨B, hB, hBH⟩

theorem hasHamiltonChartHandleStraightening_two_of_named_inputs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    (J0 : Finset (Fin 3)) (hJ0 : J0.card = 2)
    (wall : ∀ (U : TopologicalSpace.Opens X)
      (charts : Set (OpenPartialHomeomorph U V3)),
      HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3)))
    (brown : HasBrownLocallyFlatSphereBalls)
    (dehn : ∀ charts : Set (OpenPartialHomeomorph X V3),
      HasHamiltonProtectedDehnDisks L (fun c : charts => (c : OpenPartialHomeomorph X V3)))
    (prime : ∀ charts : Set (OpenPartialHomeomorph X V3),
      HasHamiltonProtectedIrreducibleReplacement (Fin 2) (Fin 1) L
        (fun c : charts => (c : OpenPartialHomeomorph X V3)))
    (approximation : ∀ (charts : Set (OpenPartialHomeomorph X V3))
      (d : (V2 × V1) → OpenPartialHomeomorph X V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph X V3)) d R)
    (rigidity : ∀ (charts : Set (OpenPartialHomeomorph X V3))
      (d : (V2 × V1) → OpenPartialHomeomorph X V3),
      HasHamiltonRelativeTorusRigidity (Fin 2) (Fin 1) L
        (fun c : charts => (c : OpenPartialHomeomorph X V3)) d) :
    HasHamiltonChartHandleStraightening E J0 := by
  apply hasHamiltonChartHandleStraightening_of_product_case hdim (by norm_num : 0 < 2) J0 hJ0
  intro h hsource N hN hboundary hPL
  exact exists_hamilton_indexTwo_handle_straightening h hsource hN hboundary hPL
    wall brown dehn prime approximation rigidity

end PoincareConjecture.M76
