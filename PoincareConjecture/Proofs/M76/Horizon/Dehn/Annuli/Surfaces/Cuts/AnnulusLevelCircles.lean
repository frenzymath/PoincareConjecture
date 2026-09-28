import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "P2" => (ℝ × ℝ)

theorem exists_finitePL_annulus_level_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} {L d u : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (hu : u ∈ Icc (-d) d) (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL) :
    ∃ (S : Set E) (gamma : Q2 ≃ₜ S), gamma.IsFinitePL ∧ IsCompact S ∧ S ⊆ T ∧
      ∀ p : squareAnnulus L d, (c p : E) ∈ S ↔ depth L p = u := by
  classical
  have hsize : 2 * u < L := by linarith [hu.2]
  obtain ⟨e, he, heb⟩ := (_root_.Dehn.isFinitePLBallPair_annulusSquare hsize).exists_cube_chart
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let f : Q2 → squareAnnulus L d := fun q ↦
    ⟨e.symm ⟨q, sphere_subset_closedBall q.property⟩, by
      rw [mem_squareAnnulus_iff_depth]
      have hb : (e.symm ⟨q, sphere_subset_closedBall q.property⟩ : P2) ∈
          frontier (_root_.Dehn.annulusSquare L u) := by
        apply (heb _).mpr
        rw [e.apply_symm_apply, frontier_closedBall _ one_ne_zero]
        exact q.property
      rw [(_root_.Dehn.mem_frontier_annulusSquare_iff L u _).mp hb]
      exact hu⟩
  have hf : Continuous f := by
    exact (continuous_subtype_val.comp (e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _
  have hfi : Function.Injective f := by
    intro q r hqr
    have hv : (e.symm ⟨q, sphere_subset_closedBall q.property⟩ : P2) =
        e.symm ⟨r, sphere_subset_closedBall r.property⟩ :=
      congrArg (fun x : squareAnnulus L d ↦ (x : P2)) hqr
    exact Subtype.ext (congrArg (fun x : closedBall (0 : V2) 1 ↦ (x : V2))
      (e.symm.injective (Subtype.ext hv)))
  have hdepth (q : Q2) : depth L (f q : P2) = u := by
    apply (_root_.Dehn.mem_frontier_annulusSquare_iff L u _).mp
    apply (heb _).mpr
    rw [e.apply_symm_apply, frontier_closedBall _ one_ne_zero]
    exact q.property
  have hsur (p : squareAnnulus L d) (hp : depth L p = u) : ∃ q, f q = p := by
    have hpS : (p : P2) ∈ _root_.Dehn.annulusSquare L u :=
      (_root_.Dehn.mem_annulusSquare_iff L u _).mpr hp.ge
    have hb : (e ⟨p, hpS⟩ : V2) ∈ Q2 := by
      rw [← frontier_closedBall _ one_ne_zero]
      exact (heb _).mp ((_root_.Dehn.mem_frontier_annulusSquare_iff L u _).mpr hp)
    refine ⟨⟨e ⟨p, hpS⟩, hb⟩, Subtype.ext ?_⟩
    exact congrArg (fun x : _root_.Dehn.annulusSquare L u ↦ (x : P2))
      (e.symm_apply_apply ⟨p, hpS⟩)
  let S : Set E := range (fun q ↦ (c (f q) : E))
  let g : Q2 → S := fun q ↦ ⟨c (f q), mem_range_self _⟩
  have hg : Continuous g :=
    (continuous_subtype_val.comp (c.continuous.comp hf)).subtype_mk _
  have hgi : Function.Injective g := by
    intro q r hqr
    exact hfi (c.injective (Subtype.ext (congrArg (fun x : S ↦ (x : E)) hqr)))
  have hgs : Function.Surjective g := by
    rintro ⟨x, q, rfl⟩
    exact ⟨q, rfl⟩
  let gamma : Q2 ≃ₜ S := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective g ⟨hgi, hgs⟩) hg
  have hcompact : IsCompact S := isCompact_range (continuous_subtype_val.comp (c.continuous.comp hf))
  have hPL : gamma.IsFinitePL := by
    obtain ⟨a, ha, hav⟩ := he.symm
    obtain ⟨b, hb, hbv⟩ := hc
    obtain ⟨R, hR, hRs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
    have haQ : FinitePiecewiseAffineOn a Q2 := hRs ▸
      ha.restrict R hR (hRs.symm ▸ sphere_subset_closedBall)
    have hmap : MapsTo a Q2 (squareAnnulus L d) := by
      intro q hq
      rw [← hav ⟨q, sphere_subset_closedBall hq⟩]
      exact (f ⟨q, hq⟩).property
    refine ⟨b ∘ a, hb.comp haQ hmap, ?_⟩
    intro q
    change (c (f q) : E) = b (a q)
    rw [hbv (f q)]
    exact congrArg b (hav ⟨q, sphere_subset_closedBall q.property⟩)
  refine ⟨S, gamma, hPL, hcompact, ?_, ?_⟩
  · rintro x ⟨q, rfl⟩
    exact (c (f q)).property
  · intro p
    constructor
    · rintro ⟨q, hq⟩
      have hqp : f q = p := c.injective (Subtype.ext hq)
      exact hqp ▸ hdepth q
    · intro hp
      obtain ⟨q, rfl⟩ := hsur p hp
      exact mem_range_self _

end PoincareConjecture.M76.Dehn.Annuli
