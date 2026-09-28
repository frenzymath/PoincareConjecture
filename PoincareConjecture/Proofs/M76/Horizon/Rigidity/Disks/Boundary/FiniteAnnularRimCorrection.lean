import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.FiniteModelDiskCorrection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.FiniteEssentialOutputPolygon
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.EssentialPolygonAnnuli










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)



theorem OriginalFiniteCollarModel.exists_proper_disk_of_essential_annular_rim
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (M : OriginalFiniteCollarModel e R)
    {T : Set (M.vertices → ℝ × V3)} (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (hT : T ⊆ M.boundary.space)
    (j : V2 → (M.vertices → ℝ × V3)) (hj : FinitePiecewiseAffineOn j D2)
    (hi : InjOn j D2) (hjK : MapsTo j D2 M.complex.space)
    (rim : C(Q2, T)) (hjb : ∀ x : Q2, j x = (rim x : M.vertices → ℝ × V3))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map rim.continuous)) ≠ 1)
    (hdepth : ∀ x : Q2, depth 1 (c.symm (rim x)) ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ)) :
    ∃ D : Set (M.vertices → ℝ × V3),
      IsFinitePLBallPair V2 D
        (annulusChartImage c (frontier (_root_.Dehn.annulusSquare 1 0))) ∧
      D ⊆ M.complex.space ∧ D ∩ M.boundary.space =
        annulusChartImage c (frontier (_root_.Dehn.annulusSquare 1 0)) := by
  obtain ⟨n, P, hP, hPi, _, htransport, hinner, houter⟩ :=
    exists_finite_essential_output_polygon c hc j hj hi rim hjb hessential hdepth
  obtain ⟨a₀, a₁, ha₀, ha₁, hA₀, hA₁, h₀inner, h₁inner, h₀outer, h₁outer⟩ :=
    exists_essential_polygon_annuli P hP hPi
      (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : 4 * (1 / 8 : ℝ) < 1)
      hinner houter
  have hB : IsFinitePLBallPair P2 (j '' D2) (annulusChartImage c (P.boundary ℝ)) := by
    rw [htransport]
    exact ((isFinitePLBallPair_unit_cube (ι := Fin 2)).image hj hi).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨b₀, hb₀, _, _, hb₀depth⟩ := exists_transported_boundary_annulus c hc hA₀ a₀ ha₀
  obtain ⟨b₁, hb₁, _, _, hb₁depth⟩ := exists_transported_boundary_annulus c hc hA₁ a₁ ha₁
  obtain ⟨D, hD, hDK, hfront⟩ := M.exists_proper_disk_boundary_correction
    hB (image_subset_iff.mpr hjK) b₀ b₁ hb₀ hb₁
    ((annulusChartImage_subset c _).trans hT)
    ((annulusChartImage_subset c _).trans hT)
    ((hb₀depth 1).trans (congrArg (annulusChartImage c) h₀inner))
    ((hb₁depth 1).trans (congrArg (annulusChartImage c) h₁inner))
    ((hb₀depth (-1)).trans (congrArg (annulusChartImage c) h₀outer))
    ((hb₁depth (-1)).trans (congrArg (annulusChartImage c) h₁outer))
  exact ⟨D, hD.model_equiv (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm, hDK, hfront⟩

end PoincareConjecture.M76
