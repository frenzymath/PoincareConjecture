import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Planar.SourceCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry Metric Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "A" => (V1 × V2)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem exists_marked_planar_annulus_reparametrization
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X E}
    (K : SimplicialComplex ℝ A)
    (hKs : K.space = ProtectedAnnulus.source)
    {j : A → X} (hj : PolyhedralPLInCharts e j K.space)
    (hji : IsEmbedding (fun x : K.space => j x))
    {R : Set X} {F : Bool → Set X}
    (hjR : MapsTo j K.space R)
    (hproper : ∀ x : K.space,
      j x ∈ frontier R ↔ (x : A).1 ∈ sphere (0 : V1) 1)
    (hjF : ∀ b (z : sphere (0 : V2) 1), j (ProtectedAnnulus.endpoint b, z) ∈ F b) :
    ∃ (period : Circle ≃ₜ sphere (0 : V2) 1) (H : Ann ≃ₜ K.space) (g : P2 → X),
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ x : Ann, g x = j (H x)) ∧
      (∀ b z, (H (annulusRimPoint b z) : A) = (ProtectedAnnulus.endpoint b, (period z : V2))) ∧
      PolyhedralPLInCharts e g Ann ∧ IsEmbedding (fun x : Ann => g x) ∧
      MapsTo g Ann R ∧
      (∀ x : Ann, g x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      (∀ b z, g (annulusRimPoint b z) ∈ F b) ∧ g '' Ann = j '' K.space := by
  obtain ⟨period, H, _, hH, hHi, hHv, hHr⟩ :=
    ProtectedAnnulus.exists_planar_source_coordinates hKs
  obtain ⟨L, hL, hLv⟩ := hH
  let g := j ∘ L
  have hvalue (x : Ann) : g x = j (H x) := congrArg j (hLv x).symm
  have hmap : MapsTo L Ann K.space := by
    intro x hx
    rw [← hLv ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  obtain ⟨D, hD, hDs, hLD⟩ := hL
  have hg : PolyhedralPLInCharts e g Ann := by
    have hh := hj.comp_finitePiecewiseAffineOn D hD ⟨D, hD, rfl, hLD⟩
      (fun x hx => hmap (hDs.subset hx))
    simpa only [hDs] using hh
  refine ⟨period, H, g, ⟨L, ⟨D, hD, hDs, hLD⟩, hLv⟩, hHi, hvalue, hHv,
    hg, ?_, fun x hx => hjR (hmap hx), ?_, ?_, ?_⟩
  · have heq : (fun x : Ann => g x) = (fun x : K.space => j x) ∘ H :=
      funext hvalue
    rw [heq]
    exact hji.comp H.isEmbedding
  · intro x
    rw [hvalue, hproper]
    have hr := hHr x
    have hs := hKs.subset (H x).property
    exact (and_iff_left hs.2).symm.trans hr
  · intro b z
    rw [hvalue, hHv]
    exact hjF b (period z)
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨L x, hmap hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨H.symm ⟨x, hx⟩, (H.symm ⟨x, hx⟩).property, ?_⟩
      rw [hvalue, H.apply_symm_apply]

end PoincareConjecture.M76.Dehn
