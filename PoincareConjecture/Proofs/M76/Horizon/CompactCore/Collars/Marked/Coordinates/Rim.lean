import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.PrescribedTwoIntervalCircle
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.RimCoordinates

set_option autoImplicit false

open Set Geometry

namespace Set

theorem IsFinitePLBallPair.exists_boundary_homeomorph_at_two_points
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {D Q : Set E} {D' Q' : Set F}
    (hD : IsFinitePLBallPair (ℝ × ℝ) D Q)
    (hD' : IsFinitePLBallPair (ℝ × ℝ) D' Q')
    {a b : E} {c d : F} (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b)
    (hc : c ∈ Q') (hd : d ∈ Q') (hcd : c ≠ d) :
    ∃ H : Q ≃ₜ Q', H.IsFinitePL ∧ (H ⟨a, ha⟩ : F) = c ∧ (H ⟨b, hb⟩ : F) = d := by
  obtain ⟨U, V, hU, hV, hUV, hUVint⟩ := hD.exists_boundary_arcs ha hb hab
  obtain ⟨W, Z, hW, hZ, hWZ, hWZint⟩ := hD'.exists_boundary_arcs hc hd hcd
  obtain ⟨p0, hp0, hp00, hp01⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨p1, hp1, hp10, hp11⟩ := hV.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨q0, hq0, hq00, hq01⟩ := hW.exists_unitInterval_chart_with_endpoints hcd
  obtain ⟨q1, hq1, hq10, hq11⟩ := hZ.exists_unitInterval_chart_with_endpoints hcd
  obtain ⟨G, hG, hleft, _⟩ := PoincareConjecture.M76.Dehn.exists_prescribed_two_interval_homeomorph
    hUVint hWZint p0 p1 q0 q1 hp0 hp1 hq0 hq1 hp00 hp01 hp10 hp11 hq00 hq01 hq10 hq11
  let H := (Homeomorph.setCongr hUV.symm).trans (G.trans (Homeomorph.setCongr hWZ))
  refine ⟨H, hG.setCongr hUV hWZ, ?_, ?_⟩
  · have heq : (⟨a, hUV.symm.subset ha⟩ : (U ∪ V : Set E)) = ⟨p0 0, Or.inl (p0 0).property⟩ :=
      Subtype.ext hp00.symm
    change (G ⟨a, hUV.symm.subset ha⟩ : F) = c
    rw [heq]
    exact (hleft 0).trans hq00
  · have heq : (⟨b, hUV.symm.subset hb⟩ : (U ∪ V : Set E)) = ⟨p0 1, Or.inl (p0 1).property⟩ :=
      Subtype.ext hp01.symm
    change (G ⟨b, hUV.symm.subset hb⟩ : F) = d
    rw [heq]
    exact (hleft 1).trans hq01

end Set

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

open Metric

local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem isFinitePLBallPair_planar_square : IsFinitePLBallPair (ℝ × ℝ) Disk Rim :=
  (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

theorem exists_rim_homeomorph_at_two_points
    (ends : Bool → V2) (hends : ∀ b, ends b ∈ Rim)
    (hne : ends false ≠ ends true) :
    ∃ H : Rim ≃ₜ Rim, H.IsFinitePL ∧
      ∀ b, (H ⟨armPoint b (1 / 2), (armPoint_mem b (by norm_num)).1⟩ : V2) = ends b := by
  have hmark (b : Bool) : armPoint b (1 / 2) ∈ Rim :=
    (armPoint_mem b (by norm_num)).1
  have hdistinct : armPoint false (1 / 2) ≠ armPoint true (1 / 2) := by
    intro h
    have hc := congrFun h 0
    norm_num [armPoint, TubeExterior.CornerBands.sign] at hc
  obtain ⟨H, hH, hfalse, htrue⟩ :=
    isFinitePLBallPair_planar_square.exists_boundary_homeomorph_at_two_points
      isFinitePLBallPair_planar_square (hmark false) (hmark true) hdistinct
      (hends false) (hends true) hne
  exact ⟨H, hH, fun b ↦ by cases b <;> assumption⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
