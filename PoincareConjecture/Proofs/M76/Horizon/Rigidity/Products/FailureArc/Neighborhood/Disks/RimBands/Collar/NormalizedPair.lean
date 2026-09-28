import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Reflection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.CapSides









set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_unsigned_marked_disk_products
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r w : ℝ} {j : Bool → V2 → X}
    (P : ∀ side, OriginalDiskProduct e (R \ U.map '' openTube r) (j side))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ) (o : Bool → Bool → Bool)
    (hmark : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      (P side).map (z, s) = F side (z, (w / ρ side) * s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t, s) =
        prescribedArmBand U r (ρ side) 0 1 side b (sign (o side b) * s, t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ side, ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P side).map '' (Disk ×ˢ Ioo (-v) v))))
    (hcoherent : ∀ side, o side false = o side true) :
    ∃ (P' : ∀ side, OriginalDiskProduct e (R \ U.map '' openTube r) (j side))
      (F' : Bool → V2 × ℝ → X),
      (∀ side, (P' side).map = (P side).map ∘ bandTimeScale (sign (o side false))) ∧
      (∀ side, F' side = F side ∘ bandTimeScale (sign (o side false))) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        (P' side).map (z, s) = F' side (z, (w / ρ side) * s)) ∧
      (∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
        F' side (rimArmPoint b t, s) = prescribedArmBand U r (ρ side) 0 1 side b (s, t)) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        F' side (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t) ∧
      Disjoint ((P' false).map '' (Disk ×ˢ J)) ((P' true).map '' (Disk ×ˢ J)) ∧
      (∀ side, ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
          ((P' side).map '' (Disk ×ˢ Ioo (-v) v)))) ∧
      (∀ side a, (P' side).map '' (Disk ×ˢ Icc (-a) a) =
        (P side).map '' (Disk ×ˢ Icc (-a) a)) ∧
      ∀ side a, (P' side).map '' (Disk ×ˢ Ioo (-a) a) =
        (P side).map '' (Disk ×ˢ Ioo (-a) a) := by
  classical
  choose P' hP hclosed hopenImage using fun side =>
    exists_reflected_original_disk_product (P side) (o side false)
  let F' : Bool → V2 × ℝ → X := fun side => F side ∘ bandTimeScale (sign (o side false))
  refine ⟨P', F', hP, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, hclosed, hopenImage⟩
  · intro side z hz s hs
    have hsigned : sign (o side false) * s ∈ J :=
      ((bandTimeScale_sign_mem_Icc (o side false) Rim 1 (z, s)).mpr ⟨hz, hs⟩).2
    rw [hP side]
    change (P side).map (z, sign (o side false) * s) =
      F side (z, sign (o side false) * ((w / ρ side) * s))
    rw [hmark side z hz _ hsigned]
    congr 1
    apply Prod.ext
    · rfl
    · dsimp
      ring
  · intro side
    exact reflected_boundary_band_arms U (o side) (hcoherent side) (harms side)
  · intro side
    exact reflected_boundary_band_lateral U (o side false) (hlateral side)
  · rw [hclosed false 1, hclosed true 1]
    exact hdis
  · intro side v hv hv1
    rw [hopenImage side v]
    exact hopen side v hv hv1

end PoincareConjecture.M76.Dehn.Annuli.RimBands
