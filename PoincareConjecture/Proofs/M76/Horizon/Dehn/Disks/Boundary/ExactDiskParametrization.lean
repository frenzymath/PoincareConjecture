import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



theorem proper_disk_isFinitePLBallPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D R : Set E} (b : D2 ≃ₜ D) (hb : b.IsFinitePL)
    (hproper : ∀ x : D2, (b x : E) ∈ frontier R ↔ (x : V2) ∈ Q2) :
    IsFinitePLBallPair V2 D (D ∩ frontier R) := by
  apply isFinitePLBallPair_unit_cube.of_homeomorph inter_subset_left b.symm hb.symm
  intro x
  have h := hproper (b.symm x)
  rw [b.apply_symm_apply] at h
  exact ⟨fun hx ↦ h.mp hx.2, fun hx ↦ ⟨x.property, h.mpr hx⟩⟩



theorem exists_exact_proper_disk_parametrization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D S R : Set E} (hD : IsFinitePLBallPair V2 D S)
    (hfront : D ∩ frontier R = S) (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL) :
    ∃ b : D2 ≃ₜ D, b.IsFinitePL ∧
      (∀ x : Q2, (b ⟨x, sphere_subset_closedBall x.property⟩ : E) = (gamma x : E)) ∧
      ∀ x : D2, (b x : E) ∈ frontier R ↔ (x : V2) ∈ Q2 := by
  obtain ⟨b, hb, hvalues, hboundary⟩ :=
    isFinitePLBallPair_unit_cube.exists_extension hD gamma hgamma
  refine ⟨b, hb, fun x ↦ congrArg Subtype.val (hvalues x), ?_⟩
  intro x
  have hmem : (b x : E) ∈ S ↔ (b x : E) ∈ frontier R := by
    rw [← hfront]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(b x).property, h⟩⟩
  exact hmem.symm.trans (hboundary x).symm

end PoincareConjecture.M76.Dehn
