import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CapRectangles
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.LateralArms



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

noncomputable def rimArmPoint (b : Bool) (t : ℝ) : V2 := ![sign b,2*t-1]

theorem fromRectangle_arm (b : Bool) (t : ℝ) :
    CubeCoordinates.fromRectangle (if b then 0 else 1,t) = rimArmPoint b t := by
  cases b <;> norm_num [CubeCoordinates.fromRectangle,rimArmPoint,sign]

theorem rimArmPoint_mem_rim (b : Bool) {t : ℝ} (ht : t ∈ I) : rimArmPoint b t ∈ Rim := by
  apply (CubeCoordinates.toRectangle_rim_iff _).mp
  rw [← fromRectangle_arm,CubeCoordinates.toRectangle_fromRectangle]
  have hfront : frontier Rect =
      (I ×ˢ ({0,1} : Set ℝ)) ∪ (({0,1} : Set ℝ) ×ˢ I) := by
    rw [frontier_prod_eq,isClosed_Icc.closure_eq,frontier_Icc zero_le_one]
  rw [hfront]
  apply Or.inr
  exact ⟨by cases b <;> simp,ht⟩

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R Q W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : V2 → X}

omit [T2Space X] in
theorem capRectangle_arm_parameter (P : OriginalDiskProduct e Q j)
    (s : ℝ) (b : Bool) (t : ℝ) :
    capRectangle P s (if b then 0 else 1,t) = P.map (rimArmPoint b t,s) := by
  simp only [capRectangle,fromRectangle_arm]

omit [T2Space X] in
theorem capRectangle_prescribed_arm_edges
    (P : OriginalDiskProduct e Q j) (F : V2 × ℝ → X)
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r δ t₀ t₁ : ℝ) (side : Bool) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z,s) = F (z,a*s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F (rimArmPoint b t,s) = prescribedArmBand U r δ t₀ t₁ side b (s,t)) :
    ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      capRectangle P s (if b then 0 else 1,t) =
        originalBandMap U r (b,if side then !b else b)
          ((δ*a)*(sign b*s),(1-t)*t₀+t*t₁) := by
  intro b t ht s hs
  have has : a*s ∈ J := by constructor <;> nlinarith [hs.1,hs.2]
  rw [capRectangle_arm_parameter,hmark _ (rimArmPoint_mem_rim b ht) s hs,
    harms b t ht _ has]
  change originalBandMap U r (b,if side then !b else b)
    (armCoordinates δ t₀ t₁ b (a*s,t)) = _
  rw [armCoordinates_apply]
  congr 2
  ring

omit [T2Space X] in
theorem capRectangle_common_width_arm_edges
    (P : OriginalDiskProduct e Q j) (F : V2 × ℝ → X)
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r : ℝ) (side : Bool) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 < w)
    (hwρ : w/ρ ≤ 1)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z,s) = F (z,(w/ρ)*s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F (rimArmPoint b t,s) = prescribedArmBand U r ρ 0 1 side b (s,t)) :
    ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      capRectangle P s (if b then 0 else 1,t) =
        originalBandMap U r (b,if side then !b else b) (w*(sign b*s),t) := by
  have h := capRectangle_prescribed_arm_edges P F U r ρ 0 1 side
    (div_pos hw hρ) hwρ hmark harms
  simpa only [mul_div_cancel₀ _ hρ.ne',mul_zero,mul_one,zero_add] using h

end PoincareConjecture.M76.Dehn.Annuli
