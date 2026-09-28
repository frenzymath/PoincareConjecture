import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProductBandSides
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneActualMeridian

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)
local notation "Io" => Ioo (-(1 / 4 : ℝ)) (1 / 4)

theorem exists_original_prescribed_product_band {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {R D : Set E} {b : D2 ≃ₜ D} (P : HamiltonUnmarkedDiskProduct R b)
    (e : frontier squareShell ≃ₜ frontier R) (he : e.IsFinitePL)
    (hboundary : ∀ (x : Q2) (hx : standardSquareMeridian x ∈ frontier squareShell),
      (b ⟨x, sphere_subset_closedBall x.property⟩ : E) =
        e ⟨standardSquareMeridian x, hx⟩) :
    ∃ F : (V2 × ℝ) → E, FinitePiecewiseAffineOn F (Q2 ×ˢ I) ∧
      InjOn F (Q2 ×ˢ I) ∧ MapsTo F (Q2 ×ˢ I) (frontier R) ∧
      (∀ x ∈ Q2, F (x, 0) = P.map (x, 0)) ∧
      IsOpen ((Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io))) ∧
      ∀ (p : V2 × ℝ) (_hp : p ∈ Q2 ×ˢ I)
        (hs : standardMeridianBandMap p ∈ frontier squareShell),
        F p = e ⟨standardMeridianBandMap p, hs⟩ := by
  obtain ⟨v, hv, heval⟩ := he
  obtain ⟨hstd, hstdi, hstdm, hzero, hopen⟩ := standardMeridianBandMap_properties
  let F : (V2 × ℝ) → E := v ∘ standardMeridianBandMap
  have hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I) := hv.comp hstd hstdm
  have hvalue (p : V2 × ℝ) (hs : standardMeridianBandMap p ∈ frontier squareShell) :
      F p = e ⟨standardMeridianBandMap p, hs⟩ :=
    (heval ⟨standardMeridianBandMap p, hs⟩).symm
  have hFi : InjOn F (Q2 ×ˢ I) := by
    intro p hp q hq hpq
    apply hstdi hp hq
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hvalue p (hstdm hp)).symm.trans (hpq.trans (hvalue q (hstdm hq))))))
  have hFm : MapsTo F (Q2 ×ˢ I) (frontier R) := by
    intro p hp
    rw [hvalue p (hstdm hp)]
    exact (e ⟨standardMeridianBandMap p, hstdm hp⟩).property
  have hcenter (x : V2) (hx : x ∈ Q2) : F (x, 0) = P.map (x, 0) := by
    have hp : (x, (0 : ℝ)) ∈ Q2 ×ˢ I := ⟨hx, by norm_num⟩
    have hz : standardMeridianBandMap (x, 0) = standardSquareMeridian x := hzero ⟨x, hx⟩
    have hs : standardSquareMeridian x ∈ frontier squareShell := hz ▸ hstdm hp
    have hbe := hboundary ⟨x, hx⟩ hs
    have harg : (⟨standardMeridianBandMap (x, 0), hstdm hp⟩ : frontier squareShell) =
        ⟨standardSquareMeridian x, hs⟩ := Subtype.ext hz
    exact (hvalue (x, 0) (hstdm hp)).trans
      ((congrArg (fun y : frontier squareShell => (e y : E)) harg).trans
        (hbe.symm.trans (P.central ⟨x, sphere_subset_closedBall hx⟩).symm))
  have hsets : (Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io)) =
      e.symm ⁻¹' ((Subtype.val : frontier squareShell → W) ⁻¹'
        (standardMeridianBandMap '' (Q2 ×ˢ Io))) := by
    ext y
    constructor
    · rintro ⟨p, hp, hpy⟩
      have hpI : p ∈ Q2 ×ˢ I := ⟨hp.1, Ioo_subset_Icc_self hp.2⟩
      have hey : e ⟨standardMeridianBandMap p, hstdm hpI⟩ = y :=
        Subtype.ext ((hvalue p (hstdm hpI)).symm.trans hpy)
      have hback := congrArg e.symm hey
      rw [e.symm_apply_apply] at hback
      exact ⟨p, hp, congrArg Subtype.val hback⟩
    · rintro ⟨p, hp, hpy⟩
      have hpI : p ∈ Q2 ×ˢ I := ⟨hp.1, Ioo_subset_Icc_self hp.2⟩
      have hback : (⟨standardMeridianBandMap p, hstdm hpI⟩ : frontier squareShell) =
          e.symm y := Subtype.ext hpy
      refine ⟨p, hp, ?_⟩
      rw [hvalue p (hstdm hpI), hback, e.apply_symm_apply]
  refine ⟨F, hF, hFi, hFm, hcenter, ?_, fun p _ hs => hvalue p hs⟩
  rw [hsets]
  exact hopen.preimage e.symm.continuous

end PoincareConjecture.M76.HamiltonIndexOne
