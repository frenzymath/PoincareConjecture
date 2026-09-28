import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.StandardBoundaryAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.MarkedLoopImage
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.AnnulusRetraction
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall










set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)

theorem finitePiecewiseAffineOn_standard_disk
    {R : Set V3}
    (he : PLDomain (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    {j : V2 → V3}
    (hj : PolyhedralPLInCharts
      (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) j D2) :
    FinitePiecewiseAffineOn j D2 := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2))
  have h := PolyhedralPLInCharts.finitePiecewiseAffineOn_fixed_chart he.compatible
    K hK (hKs ▸ hj) () (by intro x hx; trivial)
  change FinitePiecewiseAffineOn j K.space at h
  rwa [hKs] at h




theorem exists_standard_essential_boundary_disk
    {R S : Set V3} (hR : IsCompact R)
    (he : PLDomain (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hS : S ⊆ frontier R) (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL)
    (f : C(D2, R))
    (hboundary : ∀ x : Q2,
      (f ⟨x, sphere_subset_closedBall x.property⟩ : V3) = (gamma x : V3)) :
    ∃ (T : Set V3) (c : Ann ≃ₜ T),
      T ⊆ frontier R ∧ S ⊆ T ∧ c.IsFinitePL ∧
      (∀ p : Ann, (c p : V3) ∈ S ↔ depth 1 p = 0) ∧
      ∃ (j : V2 → V3) (rim : C(Q2, T)),
        FinitePiecewiseAffineOn j D2 ∧ InjOn j D2 ∧ MapsTo j D2 R ∧
        (∀ x : Q2, j x = (rim x : V3)) ∧
        (∀ x : D2, j x ∈ frontier R ↔ (x : V2) ∈ Q2) ∧
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (squareRimLoop.map rim.continuous)) ≠ 1 ∧
        ∀ x : Q2, depth 1 (c.symm (rim x)) ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) := by
  obtain ⟨T, c, _, hTB, hST, hc, _, hcore, F, O, U, _, _, _, _, _, hSF,
    hFT, hFB, hFopen, _, hdepth⟩ :=
    exists_standard_boundary_circle_annulus hR he hS gamma hgamma
  let gammaF : C(Q2, F) := ⟨fun x ↦ ⟨gamma x, hSF (gamma x).property⟩,
    (continuous_subtype_val.comp gamma.continuous).subtype_mk _⟩
  let u : C(F, T) := ⟨fun x ↦ ⟨x, hFT x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  have hessential : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((squareRimLoop.map gammaF.continuous).map u.continuous)) ≠ 1 := by
    have h := squareRimLoop_class_ne_one_in_annulus_neighborhood
      (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : 4 * (1 / 8 : ℝ) < 1)
      hST (Subset.rfl : T ⊆ T) c hcore gamma (u.comp gammaF) (fun _ ↦ rfl)
    exact h
  obtain ⟨j, rimF, hj, hi, hjR, hjb, hjp, hje⟩ :=
    exists_marked_boundary_disk_with_essential_image
      (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) R he
      F hFB hFopen f gammaF hboundary u hessential
  refine ⟨T, c, hTB, hST, hc, hcore, j, u.comp rimF,
    finitePiecewiseAffineOn_standard_disk he hj, ?_, hjR, hjb, hjp, hje, ?_⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (hi.injective (show (fun x : D2 ↦ j x) ⟨x, hx⟩ =
      (fun x : D2 ↦ j x) ⟨y, hy⟩ from hxy))
  · intro x
    exact hdepth (u (rimF x)) (rimF x).property

end PoincareConjecture.M76.Dehn
