import PoincareConjecture.Proofs.M76.Rigidity.OriginalBandCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedBandOpenness
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.isOpen_prescribed_band_coordinates
    (P : OriginalDiskProduct e R j) (F : E → X) (k : X → E) {a : ℝ}
    (hleft : ∀ z ∈ D ×ˢ I, k (P.map z) = z)
    (hback : ∀ z ∈ Q ×ˢ Icc (-a) a, P.map (k (F z)) = F z)
    (hcoord : MapsTo (k ∘ F) (Q ×ˢ Icc (-a) a)
      (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      (F '' (Q ×ˢ Ioo (-a) a)))) :
    IsOpen ((fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹'
      ((k ∘ F) '' (Q ×ˢ Ioo (-a) a))) := by
  let L : Set (Q × ℝ) := {z | z.2 ∈ I}
  let T : Set (Q × ℝ) := (fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹'
    ((k ∘ F) '' (Q ×ˢ Ioo (-a) a))
  let W : Set (Q × ℝ) := {z | z.2 ∈ Ioo (-1 : ℝ) 1}
  have hLI (z : L) : (((z : Q × ℝ).1 : V2), (z : Q × ℝ).2) ∈ D ×ˢ I :=
    ⟨sphere_subset_closedBall z.val.1.property, z.property⟩
  let f : L → frontier R := fun z =>
    ⟨P.map (((z : Q × ℝ).1 : V2), (z : Q × ℝ).2),
      (P.proper _ (hLI z)).mpr z.val.1.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact P.polyhedral.continuousOn.comp_continuous
      (by fun_prop) hLI
  have heq : f ⁻¹' ((Subtype.val : frontier R → X) ⁻¹'
      (F '' (Q ×ˢ Ioo (-a) a))) = (Subtype.val : L → Q × ℝ) ⁻¹' T := by
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      refine ⟨w, hw, ?_⟩
      change k (F w) = (((z : Q × ℝ).1 : V2), (z : Q × ℝ).2)
      change F w = P.map (((z : Q × ℝ).1 : V2), (z : Q × ℝ).2) at hwz
      rw [hwz, hleft _ (hLI z)]
    · rintro ⟨w, hw, hwz⟩
      refine ⟨w, hw, ?_⟩
      change F w = P.map (((z : Q × ℝ).1 : V2), (z : Q × ℝ).2)
      exact (hback w ⟨hw.1, Ioo_subset_Icc_self hw.2⟩).symm.trans
        (congrArg P.map hwz)
  have hpre : IsOpen ((Subtype.val : L → Q × ℝ) ⁻¹' T) :=
    heq ▸ hopen.preimage hf
  have hTW : T ⊆ W := by
    rintro z ⟨w, hw, hwz⟩
    have hc := hcoord ⟨hw.1, Ioo_subset_Icc_self hw.2⟩
    rw [hwz] at hc
    exact ⟨by linarith [hc.2.1], by linarith [hc.2.2]⟩
  have hWL : W ⊆ L := fun _ hz => Ioo_subset_Icc_self hz
  have himage : (Subtype.val : L → Q × ℝ) ''
      ((Subtype.val : L → Q × ℝ) ⁻¹' T) = T := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · intro z hz
      exact ⟨⟨z, hWL (hTW hz)⟩, hz, rfl⟩
  have hW : IsOpen W := isOpen_Ioo.preimage continuous_snd
  have himageW : (Subtype.val : L → Q × ℝ) ''
      ((Subtype.val : L → Q × ℝ) ⁻¹' T) ⊆ W := himage.subset.trans hTW
  have hWrange : W ⊆ range (Subtype.val : L → Q × ℝ) :=
    fun z hz => ⟨⟨z, hWL hz⟩, rfl⟩
  have hT := Topology.IsEmbedding.subtypeVal.isInducing.isOpen_image_of_subset_open
    hpre hW himageW hWrange
  change IsOpen T
  rw [← himage]
  exact hT

end PoincareConjecture.M76
