import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleCoordinates.SourceAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

theorem exists_planar_source_coordinates {S : Set (V1 × V2)} (hS : S = source) :
    ∃ (j : Circle ≃ₜ sphere (0 : V2) 1) (H : Ann ≃ₜ S),
      FinitePiecewiseAffineOn
        (fun s : ℝ ↦ (j ((32 * s : ℝ) : Circle) : V2)) (Icc 0 1) ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ b z, (H (annulusRimPoint b z) : V1 × V2) = (endpoint b, (j z : V2))) ∧
      ∀ x : Ann, (H x : V1 × V2) ∈ Rim ↔ depth 8 x = -1 ∨ depth 8 x = 1 := by
  classical
  obtain ⟨j, G, hj, hG, hGi, _, hvalue⟩ := exists_source_square_annulus_coordinates
  let H := G.symm.trans (Homeomorph.setCongr hS.symm)
  have hHvalue (b : Bool) (z : Circle) :
      (H (annulusRimPoint b z) : V1 × V2) = (endpoint b, (j z : V2)) := hvalue b z
  refine ⟨j, H, hj, hGi.setCongr rfl hS.symm, (hGi.setCongr rfl hS.symm).symm,
    hHvalue, ?_⟩
  intro x
  have hrim (b : Bool) (z : Circle) : (H (annulusRimPoint b z) : V1 × V2) ∈ Rim := by
    rw [hHvalue]
    exact ⟨endpoint_mem_sphere b, (j z).property⟩
  constructor
  · intro hx
    have hconst : (H x).val.1 = fun _ ↦ (H x).val.1 0 := by
      funext k
      exact congrArg (H x).val.1 (Subsingleton.elim k 0)
    have habs : |(H x).val.1 0| = 1 := by
      have hh := mem_sphere_zero_iff_norm.mp hx.1
      rw [hconst, pi_norm_const, Real.norm_eq_abs] at hh
      exact hh
    have hendpoint : ∃ b, (H x).val.1 = endpoint b := by
      rcases abs_eq (show (0 : ℝ) ≤ 1 by norm_num) |>.mp habs with hp | hn
      · refine ⟨true, hconst.trans ?_⟩
        funext k
        exact hp
      · refine ⟨false, hconst.trans ?_⟩
        funext k
        exact hn
    obtain ⟨b, hb⟩ := hendpoint
    let z := j.symm ⟨(H x).val.2, hx.2⟩
    have heq : x = annulusRimPoint b z := by
      apply H.injective
      apply Subtype.ext
      rw [hHvalue]
      exact Prod.ext hb (congrArg Subtype.val (j.apply_symm_apply
        ⟨(H x).val.2, hx.2⟩)).symm
    rw [heq, depth_annulusRimPoint]
    cases b <;> simp
  · intro hx
    rcases hx with hx | hx
    · have hm : x ∈ range (annulusRimPoint false) := by
        rw [range_annulusRimPoint]
        exact hx
      obtain ⟨z, rfl⟩ := hm
      exact hrim false z
    · have hm : x ∈ range (annulusRimPoint true) := by
        rw [range_annulusRimPoint]
        exact hx
      obtain ⟨z, rfl⟩ := hm
      exact hrim true z

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
