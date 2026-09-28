import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.EssentialSquareRim
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusDepth

set_option autoImplicit false
open Set Metric Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_square_annulus_middle_retraction {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ r : C(squareAnnulus L d, squareAnnulus L d),
      (∀ p, depth L (r p) = 0) ∧
      ∀ p : squareAnnulus L d, depth L p = 0 → r p = p := by
  have hL : 0 < L := by linarith
  obtain ⟨e, he⟩ := exists_annulus_homeomorph hL hd.le hwidth
  have hdepth (q : AddCircle (4 * L) × Icc (-d) d) :
      depth L (e q) = (q.2 : ℝ) := by
    rw [he]
    exact depth_annulusMap hL (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (abs_le.mpr q.2.property) (by norm_num)) hwidth) q.1
  let z : Icc (-d) d := ⟨0, by constructor <;> linarith⟩
  let r : C(squareAnnulus L d, squareAnnulus L d) :=
    ⟨fun p ↦ e ((e.symm p).1, z), e.continuous.comp
      ((continuous_fst.comp e.symm.continuous).prodMk continuous_const)⟩
  refine ⟨r, fun p ↦ hdepth ((e.symm p).1, z), ?_⟩
  intro p hp
  have ht : ((e.symm p).2 : ℝ) = 0 := by
    rw [← hdepth (e.symm p), e.apply_symm_apply, hp]
  have hz : ((e.symm p).1, z) = e.symm p := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext ht.symm
  change e ((e.symm p).1, z) = p
  rw [hz, e.apply_symm_apply]

theorem exists_annulus_middle_retraction
    {X : Type*} [TopologicalSpace X] {S T : Set X} {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (hST : S ⊆ T)
    (a : squareAnnulus L d ≃ₜ T)
    (hmiddle : ∀ p, (a p : X) ∈ S ↔ depth L p = 0) :
    ∃ r : C(T, S), ∀ x : S, r ⟨x, hST x.property⟩ = x := by
  obtain ⟨r0, hzero, hfix⟩ := exists_square_annulus_middle_retraction hd hwidth
  let r : C(T, S) := ⟨fun x ↦ ⟨a (r0 (a.symm x)), (hmiddle _).mpr (hzero _)⟩,
    (continuous_subtype_val.comp (a.continuous.comp
      (r0.continuous.comp a.symm.continuous))).subtype_mk _⟩
  refine ⟨r, ?_⟩
  intro x
  have hx : depth L (a.symm ⟨x, hST x.property⟩) = 0 := by
    apply (hmiddle _).mp
    rw [a.apply_symm_apply]
    exact x.property
  apply Subtype.ext
  change (a (r0 (a.symm ⟨x, hST x.property⟩)) : X) = x
  rw [hfix _ hx, a.apply_symm_apply]

theorem squareRimLoop_class_ne_one_in_annulus_neighborhood
    {X : Type*} [TopologicalSpace X] {S F T : Set X} {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (hSF : S ⊆ F) (hFT : F ⊆ T)
    (a : squareAnnulus L d ≃ₜ T)
    (hmiddle : ∀ p, (a p : X) ∈ S ↔ depth L p = 0)
    (gamma : Q2 ≃ₜ S) (gammaF : C(Q2, F))
    (hgamma : ∀ x, (gammaF x : X) = (gamma x : X)) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gammaF.continuous)) ≠ 1 := by
  obtain ⟨r, hr⟩ := exists_annulus_middle_retraction hd hwidth (hSF.trans hFT) a hmiddle
  let inclusion : C(F, T) :=
    ⟨fun x ↦ ⟨x, hFT x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let inverse : C(S, Q2) := ⟨gamma.symm, gamma.symm.continuous⟩
  let q : C(F, Q2) := inverse.comp (r.comp inclusion)
  apply squareRimLoop_map_class_ne_one_of_retraction gammaF q
  intro x
  have heq : inclusion (gammaF x) =
      (⟨gamma x, hFT (hSF (gamma x).property)⟩ : T) := Subtype.ext (hgamma x)
  change gamma.symm (r (inclusion (gammaF x))) = x
  rw [heq, hr, gamma.symm_apply_apply]

end PoincareConjecture.M76.Dehn
