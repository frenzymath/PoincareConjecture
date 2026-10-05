import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Regions.ZeroChargeRegionBalls
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonTheoremOne

/-!
# Alexander regions and Hamilton's unconditional index-three case

The proved zero-charge base closes the existing full sphere induction and
the index-three chart handle. The four-case dispatcher retains only the
three lower-index hypotheses. See Alexander 1924, pp. 6--8, Hamilton
1976, pp. 64--68 and M76 derivation 333.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- An actual finite PL sphere in dimension three has both prescribed
Alexander region-ball certificates. The complete zero-charge base is
proved and introduces no additional premise. See Alexander pp. 6--8
and M76 derivations 278d, 329 and 333. -/
theorem IsFinitePL.hasAlexanderRegionBalls
    {S : Set E} {D : Set F} {e : S ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hDcv : Convex ℝ D) (hDne : (interior D).Nonempty)
    (hdimD : Module.finrank ℝ F = 3) (hdim : Module.finrank ℝ E = 3)
    {C : Set E} (hC : IsCompact C) (hCcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hSC : S ⊆ interior C)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJC : J.space = C) :
    HasAlexanderRegionBalls S C := by
  exact he.hasAlexanderRegionBalls_of_zero_charge_supplier hD hDcv hDne hdimD hdim
    hC hCcv hne hSC J hJ hJC
    (PoincareMT.M76.hasZeroChargeAlexanderRegionBalls hdim C hC hCcv hne J hJ hJC)

end Homeomorph

namespace PoincareMT.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Hamilton's index-three chart handle needs no geometric supplier.
Both Alexander regions and the exact chart-image identification are
constructed by the proved sphere theorem. See Hamilton p. 66 and
M76 derivations 317, 329 and 333. -/
theorem hasHamiltonChartHandleStraightening_indexThree
    (hdim : Module.finrank ℝ E = 3) :
    HasHamiltonChartHandleStraightening E Finset.univ := by
  have hcyl : coordinateCylinder (Finset.univ : Finset (Fin 3)) =
      closedBall (0 : Fin 3 → ℝ) 1 := by
    ext x
    simp only [coordinateCylinder, mem_ofPred_eq, Finset.mem_univ, forall_true_left,
      mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one, Real.norm_eq_abs]
  intro e hsource N _ hfront hPL
  rw [hcyl] at hsource hfront
  have hboundary : sphere (0 : Fin 3 → ℝ) 1 ⊆ e.source ∩ N := by
    intro x hx
    exact ⟨hsource (sphere_subset_closedBall hx),
      hfront ((frontier_closedBall _ one_ne_zero).symm.subset hx)⟩
  obtain ⟨_, _, _, A, _, hA, _, ⟨H⟩⟩ :=
    exists_indexThree_chart_handleStraightening_of_zero_charge_supplier hdim
      (hasZeroChargeAlexanderRegionBalls hdim) e hsource hPL hboundary
  refine ⟨A, hA, ⟨{ H.toHomotopy with prop' := ?_ }⟩⟩
  intro t
  refine ⟨(H.prop t).1, fun x hx => (H.prop t).2 x (by linarith), ?_⟩
  intro x hx
  apply (H.prop t).2 x
  rw [hcyl, frontier_closedBall _ one_ne_zero] at hx
  rcases hx with hx | hx
  · exact (not_le.mp (by simpa only [mem_compl_iff, mem_closedBall_zero_iff] using hx)).le
  · exact le_of_eq (mem_sphere_zero_iff_norm.mp hx).symm

/-- The four chart-handle cases now require only the three explicit
lower-index statements. The index-three case and its zero-charge sphere
input are proved. See Hamilton pp. 64--68 and derivation 333. -/
theorem hasHamiltonChartHandleStraightening_of_lower_indices
    (hdim : Module.finrank ℝ E = 3)
    (indexZero : HasHamiltonChartHandleStraightening E ∅)
    (indexOne : ∀ J : Finset (Fin 3), J.card = 1 → HasHamiltonChartHandleStraightening E J)
    (indexTwo : ∀ J : Finset (Fin 3), J.card = 2 → HasHamiltonChartHandleStraightening E J) :
    ∀ J : Finset (Fin 3), HasHamiltonChartHandleStraightening E J :=
  hasHamiltonChartHandleStraightening_of_zero_charge_and_lower_indices hdim
    (hasZeroChargeAlexanderRegionBalls hdim) indexZero indexOne indexTwo

end PoincareMT.M76
