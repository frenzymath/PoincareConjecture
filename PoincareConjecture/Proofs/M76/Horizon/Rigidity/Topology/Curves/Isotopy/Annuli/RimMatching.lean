import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PrescribedRimChart

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_annular_chart_prescribed_rims_of_radial_homotopies
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (B : Bool → Set E) (hB : ∀ b, B b ⊆ T) (gamma : ∀ b, Circle ≃ₜ B b)
    (hgamma : ∀ b, FinitePiecewiseAffineOn
      (fun s : ℝ => (gamma b ((32 * s : ℝ) : Circle) : E)) I)
    (hrim : ∀ (b : Bool) (x : Ann),
      depth 8 (x : P2) = (if b then 1 else -1) ↔ (c x : E) ∈ B b)
    (radial : C(T, Circle))
    (Hgamma : ∀ b, Nonempty
      ((⟨fun z => radial ⟨gamma b z, hB b (gamma b z).property⟩,
        radial.continuous.comp
          ((continuous_subtype_val.comp (gamma b).continuous).subtype_mk _)⟩ :
        C(Circle, Circle)).Homotopy (ContinuousMap.id Circle))) :
    ∃ H : Ann ≃ₜ T, H.IsFinitePL ∧
      ∀ (b : Bool) (z : Circle), (H (annulusRimPoint b z) : E) = (gamma b z : E) := by
  classical
  obtain ⟨q, hq, hqPL⟩ := exists_finitePL_annulus_boundary_comparisons
    c hc B hB gamma hgamma hrim
  let u (b : Bool) : C(Circle, Circle) :=
    ⟨fun z => radial (c (annulusRimPoint b z)), radial.continuous.comp
      (c.continuous.comp (continuous_annulusRimPoint b))⟩
  let H := annulus_radial_rim_homotopy ⟨c, c.continuous⟩ radial u (fun _ _ => rfl)
  have J (b : Bool) : Nonempty ((u b).Homotopy
      ⟨(q b).symm, (q b).symm.continuous⟩) := by
    obtain ⟨G⟩ := Hgamma b
    refine ⟨{
      toFun := fun z => G (z.1, (q b).symm z.2)
      continuous_toFun := G.continuous.comp
        (continuous_fst.prodMk ((q b).symm.continuous.comp continuous_snd))
      map_zero_left := ?_
      map_one_left := fun z => G.apply_one ((q b).symm z) }⟩
    intro z
    rw [G.apply_zero]
    change radial ⟨gamma b ((q b).symm z), _⟩ = radial (c (annulusRimPoint b z))
    apply congrArg radial
    apply Subtype.ext
    have h := hq b ((q b).symm z)
    rw [(q b).apply_symm_apply] at h
    exact h.symm
  obtain ⟨J0⟩ := J false
  obtain ⟨J1⟩ := J true
  obtain ⟨A, hA, hAv⟩ := exists_annulus_homotopic_rim_extension q
    (inverse_rim_homotopy q ((J0.symm.trans H).trans J1)) hqPL
  refine ⟨A.trans c, hA.trans hc, ?_⟩
  intro b z
  change (c (A (annulusRimPoint b z)) : E) = _
  rw [hAv]
  exact hq b z

end PoincareConjecture.M76.Dehn
