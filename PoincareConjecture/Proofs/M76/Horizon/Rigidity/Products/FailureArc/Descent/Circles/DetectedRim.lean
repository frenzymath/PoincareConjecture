import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Circles.Termination

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_embedded_planar_region_annulus_of_detected_rim
    {X Z ι : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Z]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (period : Circle ≃ₜ Q) {R : Set X} (he : PLDomain e R)
    (f₀ : P2 → X) (hf : PolyhedralPLInCharts e f₀ Ann)
    (hin : MapsTo f₀ Ann R)
    (hproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (projection : C(R, Z)) (rim : C(Q, Z)) (hessential : ¬ rim.Nullhomotopic)
    (hrim : ∀ u : Q,
      projection ⟨f₀ (annulusRimPoint false (period.symm u)),
        hin (annulusRimPoint false (period.symm u)).property⟩ = rim u)
    (M : SourceCircleDecomposition f₀ Ann)
    (hinterior : MapsTo f₀ (doubleLocusOn f₀ Ann) (interior R))
    (hcross : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → f₀ x = f₀ y →
      Nonempty (RawSourceCrossing e f₀ Ann R x y)) :
    ∃ (g : P2 → X) (q : Bool → Circle ≃ₜ Circle),
      PolyhedralPLInCharts e g Ann ∧ IsEmbedding (fun x : Ann ↦ g x) ∧
      MapsTo g Ann R ∧
      (∀ x ∈ Ann, g x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      ∀ b z, g (annulusRimPoint b z) = f₀ (annulusRimPoint b (q b z)) := by
  let regionRim : C(Q, R) := ⟨fun u ↦
    ⟨f₀ (annulusRimPoint false (period.symm u)),
      hin (annulusRimPoint false (period.symm u)).property⟩,
    (hf.continuousOn.domRestrict.comp
      ((continuous_annulusRimPoint false).comp period.symm.continuous)).subtype_mk _⟩
  have heq : projection.comp regionRim = rim := ContinuousMap.ext hrim
  have hregion : ¬ regionRim.Nullhomotopic := fun hh ↦
    hessential (heq ▸ hh.comp_right projection)
  exact exists_embedded_planar_region_annulus e hcompat period he f₀ hf hin hproper
    regionRim hregion (fun _ ↦ rfl) M hinterior hcross

end PoincareConjecture.M76.Dehn.Annuli
