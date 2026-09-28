import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.CarrierBallCertificates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalFiniteCapAvoidance

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem capped_atlas_balls_and_avoidance
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite κ] {W R Z : Set E} (e : ι → OpenPartialHomeomorph W V3)
    (he : PLDomain e ((Subtype.val : W → E) ⁻¹' R))
    (hR : IsCompact ((Subtype.val : W → E) ⁻¹' R))
    (hfront : frontier ((Subtype.val : W → E) ⁻¹' R) = (Subtype.val : W → E) ⁻¹' Z)
    (hrep : ∀ i, ∃ (A : Set E) (g : E → V3), FinitePiecewiseAffineOn g A ∧
      ∀ x ∈ (e i).source, (x : E) ∈ A ∧ e i x = g x)
    (D B : κ → Set E) (hD : ∀ j, IsFinitePLBallPair V3 (D j) (B j))
    (hDW : ∀ j, D j ⊆ W) (hDR : ∀ j, D j ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hDZ : Disjoint (⋃ j,D j) Z) :
    (∀ j, Nonempty (ChartwisePLBall e ((Subtype.val : W → E) ⁻¹' D j)
      ((Subtype.val : W → E) ⁻¹' B j))) ∧
    (∀ j, (Subtype.val : W → E) ⁻¹' D j ⊆ interior ((Subtype.val : W → E) ⁻¹' R)) ∧
    ∀ (S : Set W), ChartwisePLSphere e S → ∃ (F : W ≃ₜ W) (C : Set W),
      IsCompact C ∧ C ⊆ interior ((Subtype.val : W → E) ⁻¹' R) ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (F '' S)) ∧
      Disjoint (F '' S) ((Subtype.val : W → E) ⁻¹' ⋃ j,D j) := by
  classical
  have hballs (j : κ) := exists_chartwisePLBall_in_carrier e he.cover hrep (hD j) (hDW j)
  have hinside (j : κ) :
      (Subtype.val : W → E) ⁻¹' D j ⊆ interior ((Subtype.val : W → E) ⁻¹' R) := by
    intro x hx
    by_contra hn
    have hxR : x ∈ (Subtype.val : W → E) ⁻¹' R := hDR j hx
    have hxfront : x ∈ frontier ((Subtype.val : W → E) ⁻¹' R) := ⟨subset_closure hxR,hn⟩
    rw [hfront] at hxfront
    exact disjoint_left.mp hDZ (mem_iUnion.mpr ⟨j,hx⟩) hxfront
  refine ⟨hballs,hinside,?_⟩
  intro S s
  obtain ⟨F,C,hC,hCR,hfix,hPL,hinv,sF,hclear⟩ :=
    s.exists_motion_avoiding_finite_balls
      (fun j => (Subtype.val : W → E) ⁻¹' D j)
      (fun j => (Subtype.val : W → E) ⁻¹' B j)
      (fun j => Classical.choice (hballs j))
      (fun i j hij => (hdis hij).preimage Subtype.val) hR he hinside isOpen_interior hinside
  refine ⟨F,C,hC,hCR.trans inter_subset_left,hfix,hPL,hinv,sF,?_⟩
  simpa only [preimage_iUnion] using hclear

end PoincareConjecture.M76
