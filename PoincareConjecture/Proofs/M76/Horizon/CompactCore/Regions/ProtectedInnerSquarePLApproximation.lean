import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.General.ControlledManifoldPLApproximation
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1

theorem exists_protected_inner_square_PL_approximation
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (f : C(D, U))
    (hside : ∀ x : D, (3 / 4 : ℝ) ≤ ‖(x : V2)‖ → (f x : X) ∈ V) :
    ∃ q : V2 → X, PolyhedralPLInCharts e q D ∧ MapsTo q D U ∧
      ∃ H : C(unitInterval × D, U),
        (∀ x : D, H (0, x) = f x) ∧
        (∀ x : D, (H (1, x) : X) = q x) ∧
        ∀ (t : unitInterval) (x : D), (3 / 4 : ℝ) ≤ ‖(x : V2)‖ →
          (H (t, x) : X) ∈ V := by
  classical
  let := ChartedSpace.ofChartCover e hcover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodel
  let B : Set V2 := D ∩ {x | (3 / 4 : ℝ) ≤ ‖x‖}
  have hB : IsCompact B :=
    (isCompact_closedBall (0 : V2) 1).inter_right (isClosed_le continuous_const continuous_norm)
  have hBK : B ⊆ K.space := by rw [hKD]; exact inter_subset_left
  let a : V2 → X := fun x => if hx : x ∈ D then (f ⟨x, hx⟩ : X)
    else (f ⟨0, by simp⟩ : X)
  have ha (x : D) : a x = (f x : X) := by simp only [a, dif_pos x.property]
  have haK : ContinuousOn a K.space := by
    rw [hKD]
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp f.continuous).congr (fun x => (ha x).symm)
  have haL : PolyhedralPLInCharts e a (⊥ : SimplicialComplex ℝ V2).space := by
    rw [SimplicialComplex.space_bot]
    exact ⟨continuousOn_empty a, fun x => False.elim x.property⟩
  have haU : MapsTo a K.space U := by
    intro x hx
    have hxD : x ∈ D := hKD ▸ hx
    rw [ha ⟨x, hxD⟩]
    exact (f ⟨x, hxD⟩).property
  have haV : MapsTo a B V := by
    intro x hx
    rw [ha ⟨x, hx.1⟩]
    exact hside ⟨x, hx.1⟩ hx.2
  obtain ⟨q, hq, _, hqU, T, hTU, hT0, hT1, _, hTside⟩ :=
    OpenPartialHomeomorph.exists_relative_polyhedralPL_approximation_with_compact_control
      e hcompat hcover K ⊥ hK (by exact Set.finite_empty)
      (by simp [SimplicialComplex.space_bot])
      haK haL hU haU hB hBK hV haV
  let j : D → K.space := fun x => ⟨x, hKD.symm ▸ x.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let H : C(unitInterval × D, U) :=
    ⟨fun z => ⟨T (z.1, j z.2), hTU (z.1, j z.2)⟩,
      (T.continuous.comp (continuous_fst.prodMk (hj.comp continuous_snd))).subtype_mk _⟩
  refine ⟨q, hKD ▸ hq, hKD ▸ hqU, H, ?_, ?_, ?_⟩
  · intro x
    exact Subtype.ext ((hT0 (j x)).trans (ha x))
  · intro x
    exact hT1 (j x)
  · intro t x hx
    exact hTside t (j x) ⟨x.property, hx⟩

end PoincareConjecture.M76
