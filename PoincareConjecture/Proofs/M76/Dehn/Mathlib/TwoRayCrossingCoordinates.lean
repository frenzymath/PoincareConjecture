import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoRayProductStraightening
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TransverseAffinePlaneCoordinates

set_option autoImplicit false

open Set Geometry

namespace ContinuousLinearMap

local notation "V2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_standard_two_ray_crossing_coordinates
    {u v : V2} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : ∀ t : ℝ, 0 < t → u ≠ t • v) :
    ∃ H : C3 ≃ₜ C3,
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid C3 ∧ H 0 = 0 ∧
      (∀ x : C3, (H x).2 = x.2) ∧
      ∀ x : C3,
        ((∃ t : ℝ, 0 ≤ t ∧ x.1 = t • u) ∨
          (∃ t : ℝ, 0 ≤ t ∧ x.1 = t • v)) ↔ (H x).1.1 = 0 := by
  obtain ⟨w, F, hw, hFPL, hFzero, hFlast, hFwhole⟩ :=
    exists_whole_two_ray_product_straightening hu hv hne
  let P := (Submodule.span ℝ ({w} : Set V2)).toAffineSubspace
  have hdim : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ V2 := by
    have hdir : P.direction = Submodule.span ℝ ({w} : Set V2) :=
      Submodule.toAffineSubspace_direction _
    rw [hdir, finrank_span_singleton hw]
    simp only [Module.finrank_prod, Module.finrank_self]
  have hzero : (0 : V2) ∈ P := Submodule.zero_mem _
  obtain ⟨ell, hell, hlevel⟩ := P.exists_direction_height_of_codim_one hdim hzero
  have hline (x : V2) : (∃ t : ℝ, x = t • w) ↔ ell x = 0 := by
    have hx : x ∈ P ↔ ell x = 0 := by simpa only [sub_zero] using hlevel x
    rw [← hx]
    change (∃ t : ℝ, x = t • w) ↔ x ∈ Submodule.span ℝ {w}
    simp only [Submodule.mem_span_singleton, eq_comm]
  have hnonzero : ∃ x : V2, ell x ≠ 0 := by
    by_contra h
    apply hell
    apply LinearMap.ext
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  let B : C3 →ₗ[ℝ] ℝ := ell.comp (LinearMap.fst ℝ V2 ℝ)
  have hB : ∃ x : C3, x.2 = 0 ∧ B x ≠ 0 := by
    obtain ⟨x, hx⟩ := hnonzero
    exact ⟨(x, 0), rfl, hx⟩
  obtain ⟨e, hefirst, helast⟩ := B.exists_height_normalization_preserving_last hB
  let A := e.toAffineEquiv.toContinuousAffineEquiv
  let H := F.trans A.symm.toHomeomorph
  have hforward (x : C3) : H x = e.symm (F x) := rfl
  have hF : LocallyPiecewiseAffineOn F univ ∧
      LocallyPiecewiseAffineOn F.symm univ := hFPL
  have hHPL : H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid C3 := by
    constructor
    · change LocallyPiecewiseAffineOn (A.symm ∘ F) univ
      simpa only [preimage_univ, inter_univ,
        ContinuousAffineEquiv.coe_toContinuousAffineMap] using
        (locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ).comp hF.1
    · change LocallyPiecewiseAffineOn (F.symm ∘ A) univ
      simpa only [preimage_univ, inter_univ,
        ContinuousAffineEquiv.coe_toContinuousAffineMap] using hF.2.comp
        (locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ)
  refine ⟨H, hHPL, ?_, ?_, ?_⟩
  · rw [hforward, hFzero, map_zero]
  · intro x
    have h := helast (e.symm (F x))
    rw [e.apply_symm_apply] at h
    exact h.symm.trans (hFlast x)
  · intro x
    have h : ell (F x).1 = (H x).1.1 := by
      rw [hforward]
      have h := hefirst (e.symm (F x))
      rw [e.apply_symm_apply] at h
      exact h
    exact (hFwhole x).trans ((hline (F x).1).trans (by rw [h]))

end ContinuousLinearMap
