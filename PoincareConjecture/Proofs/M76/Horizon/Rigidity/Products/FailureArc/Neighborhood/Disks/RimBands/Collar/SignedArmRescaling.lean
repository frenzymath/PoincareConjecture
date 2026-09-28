import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Rescaling
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.CapSides



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem signed_arms_common_width
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : V2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : OriginalDiskProduct e Q j) (F : V2 × ℝ → X)
    (r : ℝ) (side : Bool) (o : Bool → Bool)
    {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 < w) (hwρ : w / ρ ≤ 1)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z, s) = F (z, (w / ρ) * s))
    (harms : ∀ b t, t ∈ I → ∀ s ∈ J,
      F (rimArm b t, s) = prescribedArmBand U r ρ 0 1 side b (sign (o b) * s, t)) :
    ∀ b t, t ∈ I → ∀ s ∈ J,
      P.map (rimArm b t, s) = prescribedArmBand U r w 0 1 side b (sign (o b) * s, t) := by
  intro b t ht s hs
  have ha : 0 < w / ρ := div_pos hw hρ
  have has : (w / ρ) * s ∈ J := by
    constructor <;> nlinarith [hs.1, hs.2]
  rw [hmark _ (rimArm_mem ht) s hs, harms b t ht _ has]
  simp only [prescribedArmBand, Function.comp_apply, armCoordinates_apply]
  apply congrArg (originalBandMap U r (b, if side then !b else b))
  apply Prod.ext
  · dsimp
    calc
      ρ * (sign b * (sign (o b) * (w / ρ * s))) =
          (ρ * (w / ρ)) * (sign b * (sign (o b) * s)) := by ring
      _ = w * (sign b * (sign (o b) * s)) := by rw [mul_div_cancel₀ _ hρ.ne']
  · rfl

end PoincareConjecture.M76.Dehn.Annuli.RimBands
