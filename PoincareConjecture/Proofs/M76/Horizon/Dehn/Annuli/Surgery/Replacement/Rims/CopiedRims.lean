import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Properness



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => (Set.prod Q (Icc (-1 : ℝ) 1) : Set E)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

def cylinderRimSet (b : Bool) : Set E :=
  {x | x ∈ Cyl ∧ x.2 = if b then 1 else -1}

theorem finitePL_annulus_rim_period (b : Bool) :
    FinitePiecewiseAffineOn
      (fun s : ℝ ↦ (annulusRimPoint b ((32 * s : ℝ) : Circle) : P2)) (Icc 0 1) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  let v : ℝ := if b then 1 else -1
  let p : ℝ →ᴬ[ℝ] P2 := ((32 : ℝ) • ContinuousAffineMap.id ℝ ℝ).prod
    (ContinuousAffineMap.const ℝ ℝ v)
  have hp : FinitePiecewiseAffineOn p (Icc 0 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine p⟩
  have hmap : MapsTo p (Icc 0 1) (rectangle (4 * (8 : ℝ)) 1) := by
    intro s hs
    refine ⟨⟨by change 0 ≤ 32 * s; linarith [hs.1],
      by change 32 * s ≤ 4 * 8; linarith [hs.2]⟩, ?_⟩
    change v ∈ Icc (-1 : ℝ) 1
    cases b <;> norm_num [v]
  have h := (finitePiecewiseAffineOn_wrappedStripMap
    (L := 8) (d := 1) (by norm_num) (by norm_num)).comp hp hmap
  apply h.congr
  intro s hs
  change wrappedStripMap 8 (32 * s, v) = annulusMap 8 (by norm_num) ((32 * s : ℝ), v)
  exact (annulusMap_coe (L := 8) (t := v) (by norm_num)
    (by cases b <;> norm_num [v]) ⟨by linarith [hs.1], by linarith [hs.2]⟩).symm

theorem exists_copied_rim_chart (b : Bool) {D : Set P2} {T : Set E}
    (copy : D ≃ₜ T) (hcopy : copy.IsFinitePL) (hDS : D ⊆ Ann)
    (hrim : ∀ z : Circle, (annulusRimPoint b z : P2) ∈ D)
    (hTC : T ⊆ Cyl) (hfull : cylinderRimSet b ⊆ T)
    (hlevel : ∀ x : D, (copy x).val.2 = (if b then 1 else -1) ↔
      depth 8 x = if b then 1 else -1) :
    ∃ gamma : Circle ≃ₜ cylinderRimSet b,
      (∀ z : Circle, (gamma z : E) = copy ⟨annulusRimPoint b z, hrim z⟩) ∧
      FinitePiecewiseAffineOn
        (fun s : ℝ ↦ (gamma ((32 * s : ℝ) : Circle) : E)) (Icc 0 1) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let g : Circle → cylinderRimSet b := fun z ↦
    ⟨copy ⟨annulusRimPoint b z, hrim z⟩,
      hTC (copy ⟨annulusRimPoint b z, hrim z⟩).property,
      (hlevel _).mpr (depth_annulusRimPoint b z)⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (copy.continuous.comp
      ((continuous_subtype_val.comp (continuous_annulusRimPoint b)).subtype_mk _))
  have hgi : Function.Injective g := by
    intro z w h
    have hh := copy.injective (Subtype.ext
      (congrArg (fun y : cylinderRimSet b ↦ (y : E)) h))
    exact injective_annulusRimPoint b (Subtype.ext (congrArg (fun y : D ↦ (y : P2)) hh))
  have hgs : Function.Surjective g := by
    intro x
    let y : D := copy.symm ⟨x, hfull x.property⟩
    have hxy : (copy y : E) = x := congrArg Subtype.val (copy.apply_symm_apply _)
    have hy : depth 8 y = if b then 1 else -1 := (hlevel y).mp (by
      rw [hxy]
      exact x.property.2)
    obtain ⟨z, hz⟩ := (range_annulusRimPoint b).symm.subset
      (show (⟨y, hDS y.property⟩ : Ann) ∈ {p : Ann | depth 8 (p : P2) = if b then 1 else -1}
        from hy)
    refine ⟨z, Subtype.ext ?_⟩
    change (copy ⟨annulusRimPoint b z, hrim z⟩ : E) = x
    have heq : (⟨annulusRimPoint b z, hrim z⟩ : D) = y :=
      Subtype.ext (congrArg (fun p : Ann ↦ (p : P2)) hz)
    rw [heq, hxy]
  let gamma := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hgi, hgs⟩) hg
  refine ⟨gamma, fun _ ↦ rfl, ?_⟩
  obtain ⟨F, hF, hFv⟩ := hcopy
  apply (hF.comp (finitePL_annulus_rim_period b) (fun s _ ↦ hrim _)).congr
  intro s _
  exact (hFv ⟨annulusRimPoint b ((32 * s : ℝ) : Circle), hrim _⟩).symm

end PoincareConjecture.M76.Dehn.Annuli
