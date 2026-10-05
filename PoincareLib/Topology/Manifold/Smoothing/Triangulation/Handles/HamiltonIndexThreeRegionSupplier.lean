import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonIndexThreeRegionBalls
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Spheres.FinitePLSphereRegionInduction
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexPolyhedralNeighborhood

/-!
# The zero-charge Alexander input to Hamilton's index-three case

The compact original chart image chooses its own finite convex outer
body. Finite PL sphere induction supplies both region certificates,
and the exact chart consumer supplies Hamilton's supported correction.
The sole remaining geometric hypothesis is the full existing zero-charge
region statement. See Hamilton 1976, p. 66 and M76 derivation 317.
-/

set_option autoImplicit false

open Set Metric Geometry TriangularRoofModel

namespace PoincareMT.M76

/-- The unresolved zero-charge case in Alexander's actual region
induction, for every finite convex containing body. The conclusion
includes both the bounded ball and its literal complementary exterior.
See Alexander 1924, pp. 7--8 and M76 derivations 278c and 317. -/
def HasZeroChargeAlexanderRegionBalls (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ C : Set E, IsCompact C → Convex ℝ C → (interior C).Nonempty →
    ∀ J : SimplicialComplex ℝ E, J.faces.Finite → J.space = C →
    ∀ W : AlexanderSectionProfile E,
      W.HasNonisolatedHeightSigns → W.HasFiniteHeightSignEvents →
      (∀ c, W.charge c = 0) → W.carrier ⊆ interior C →
      (∃ f : W.carrier ≃ₜ frontier (halfBall 1), f.IsFinitePL) →
      HasAlexanderRegionBalls W.carrier C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The complete index-three chart correction follows from the explicit
zero-charge Alexander base theorem. The outer body, actual boundary
parameterization, target ball and positive-charge induction are all
constructed internally. See Hamilton 1976, p. 66 and derivation 317. -/
theorem exists_indexThree_chart_handleStraightening_of_zero_charge_supplier
    (hdim : Module.finrank ℝ E = 3)
    (base : HasZeroChargeAlexanderRegionBalls E)
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) E)
    (hsource : closedBall (0 : Fin 3 → ℝ) 1 ⊆ e.source)
    {N : Set (Fin 3 → ℝ)} (hPL : LocallyPiecewiseAffineOn e N)
    (hN : sphere (0 : Fin 3 → ℝ) 1 ⊆ N) :
    ∃ g : closedBall (0 : Fin 3 → ℝ) 1 ≃ₜ
        e '' closedBall (0 : Fin 3 → ℝ) 1,
      g.IsFinitePL ∧
      (∀ x : sphere (0 : Fin 3 → ℝ) 1,
        (g ⟨x, sphere_subset_closedBall x.property⟩ : E) = e x) ∧
      ∃ A : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        (∀ x : closedBall (0 : Fin 3 → ℝ) 1, A x = e.symm (g x)) ∧
        FinitePiecewiseAffineOn (e ∘ A) (closedBall (0 : Fin 3 → ℝ) 1) ∧
        (∀ x, 1 ≤ ‖x‖ → A x = x) ∧
        Nonempty (ContinuousMap.HomotopyWith
          (ContinuousMap.id (Fin 3 → ℝ)) ⟨A, A.continuous⟩
          (fun f => IsHomeomorph f ∧ ∀ x, 1 ≤ ‖x‖ → f x = x)) := by
  have hcompact : IsCompact (e '' closedBall (0 : Fin 3 → ℝ) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn.mono hsource)
  obtain ⟨J, hJ, hcv, hJC⟩ := hcompact.exists_finite_convex_neighborhood
  have hC : IsCompact J.space := J.isCompact_space_of_finite hJ
  have hne : (interior J.space).Nonempty := by
    refine ⟨e 0, hJC ?_⟩
    exact mem_image_of_mem e (mem_closedBall_self zero_le_one)
  let eb := e.homeomorphOfImageSubsetSource
    (sphere_subset_closedBall.trans hsource) rfl
  have heb : eb.IsFinitePL := indexThree_chart_boundary_isFinitePL e hsource hPL hN
  let d := eb.symm.trans (Homeomorph.setCongr
    (frontier_closedBall (0 : Fin 3 → ℝ) one_ne_zero).symm)
  have hd : d.IsFinitePL := heb.symm.setCongr rfl
    (frontier_closedBall (0 : Fin 3 → ℝ) one_ne_zero).symm
  have hregions := hd.hasAlexanderRegionBalls_of_zero_charge_supplier
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
    (by simp : Module.finrank ℝ (Fin 3 → ℝ) = 3) hdim hC hcv hne
    ((image_mono sphere_subset_closedBall).trans hJC) J hJ rfl
    (base J.space hC hcv hne J hJ rfl)
  obtain ⟨g, hg, hgb, A, hA, hfix, hHt⟩ :=
    exists_indexThree_chart_handleStraightening_of_region_balls
    e hsource hPL hN hJC hregions
  refine ⟨g, hg, hgb, A, hA, ?_, hfix, hHt⟩
  obtain ⟨f, hf, hfg⟩ := hg
  apply hf.congr
  intro x hx
  have htarget : (g ⟨x, hx⟩ : E) ∈ e.target := by
    obtain ⟨y, hy, hye⟩ := (g ⟨x, hx⟩).property
    exact hye ▸ e.map_source (hsource hy)
  change f x = e (A x)
  rw [hA ⟨x, hx⟩, e.right_inv htarget]
  exact (hfg ⟨x, hx⟩).symm

end PoincareMT.M76
