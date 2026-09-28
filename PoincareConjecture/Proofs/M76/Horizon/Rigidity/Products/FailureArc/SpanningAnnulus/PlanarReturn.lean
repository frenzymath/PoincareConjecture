import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Original

set_option autoImplicit false
open Set Geometry Metric Topology PLAnnularStrip

namespace PoincareConjecture.M76

open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_original_cylinder_of_planar_annulus
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {F : Bool → Set X}
    (j : P2 → X) (original : C(Ann, R))
    (hj : PolyhedralPLInCharts e j Ann) (hji : IsEmbedding (fun x : Ann => j x))
    (hvalue : ∀ x : Ann, j x = (original x : X))
    (hproper : ∀ x : Ann, j x ∈ frontier R ↔ depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1)
    (hmark : ∀ b z, j (annulusRimPoint b z) ∈ F b)
    (hessential : ∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic) :
    ∃ (g : (V1 × V2) → X) (original' : C(source, R)),
      PolyhedralPLInCharts e g source ∧ IsEmbedding (fun x : source => g x) ∧
      (∀ x : source, g x = (original' x : X)) ∧
      (∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
      (∀ b (z : Q2), g (endpoint b, z) ∈ F b) ∧
      ∀ b, ¬ (sourceAnnulusRim original' b).Nullhomotopic := by
  obtain ⟨period, H, _, _, hHi, hHr, hHb⟩ :=
    exists_planar_source_coordinates (S := source) rfl
  obtain ⟨G, hGPL, hG⟩ := hHi
  let g := j ∘ G
  have hgvalue (x : source) : g x = j (H.symm x) := congrArg j (hG x).symm
  have hGAnn : MapsTo G source Ann := by
    intro x hx
    rw [← hG ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  obtain ⟨K, hK, hKs, hGK⟩ := hGPL
  have hgPL : PolyhedralPLInCharts e g source := by
    have hh := hj.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hGK⟩
      (fun x hx => hGAnn (hKs.subset hx))
    simpa only [hKs] using hh
  let original' := original.comp (⟨H.symm, H.symm.continuous⟩ : C(source, Ann))
  have hRim (b : Bool) (z : Q2) : H.symm
      ⟨(endpoint b, z), sphere_subset_closedBall (endpoint_mem_sphere b), z.property⟩ =
      annulusRimPoint b (period.symm z) := by
    apply H.injective
    apply Subtype.ext
    rw [H.apply_symm_apply, hHr, period.apply_symm_apply]
  refine ⟨g, original', hgPL, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : (fun x : source => g x) = (fun x : Ann => j x) ∘ H.symm := funext hgvalue
    rw [hh]
    exact hji.comp H.symm.isEmbedding
  · intro x
    exact (hgvalue x).trans (hvalue (H.symm x))
  · intro x
    rw [hgvalue, hproper]
    have hh := hHb (H.symm x)
    rw [H.apply_symm_apply] at hh
    exact hh.symm.trans (and_iff_left x.property.2)
  · intro b z
    rw [hgvalue ⟨(endpoint b, z), sphere_subset_closedBall (endpoint_mem_sphere b), z.property⟩,
      hRim]
    exact hmark b (period.symm z)
  · intro b hn
    have hh : (sourceAnnulusRim original' b).comp ⟨period, period.continuous⟩ =
        planarAnnulusRim original b := by
      apply ContinuousMap.ext
      intro z
      change original (H.symm ⟨(endpoint b, period z),
        sphere_subset_closedBall (endpoint_mem_sphere b), (period z).property⟩) =
        original (annulusRimPoint b z)
      rw [hRim, period.symm_apply_apply]
    exact hessential b (hh ▸ hn.comp_left ⟨period, period.continuous⟩)

end PoincareConjecture.M76
