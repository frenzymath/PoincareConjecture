import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.ArmImages

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands BoundaryAssembly PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_band_width_with_exact_lateral_partition
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ t₀ t₁ : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (side : Bool)
    {F : E → X} {o : Bool → Bool} {v : Bool → ℝ}
    (hv : ∀ b, 0 < v b ∧ v b < 1/2)
    (hF : ContinuousOn F (Rim ×ˢ I)) (hi : InjOn F (Rim ×ˢ I))
    (hcenter : ∀ z ∈ Rim, F (z,0) ∈ (if side then f₁ '' T else f₀ '' S))
    (harms : ∀ b a t, t ∈ J → ∀ u ∈ Icc (0 : ℝ) (v b),
      F (rimArm b t,2*(sign a*u))=
        prescribedArmBand U r δ t₀ t₁ side b (sign (o b)*(sign a*u),t)) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/2 ∧ (∀ b, a ≤ v b) ∧
      (∀ z ∈ Rim, ∀ s ∈ Icc (-a) a,
        F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ J, z=rimArm b t) ∧
      (∀ b t, t ∈ J → ∀ s ∈ Icc (-a) a,
        F (rimArm b t,s)=prescribedArmBand U r δ t₀ t₁ side b (sign (o b)*(s/2),t)) := by
  let m := min (v false) (v true)
  have hm : 0 < m := lt_min (hv false).1 (hv true).1
  have hmv (b : Bool) : m ≤ v b := by cases b; exact min_le_left _ _; exact min_le_right _ _
  have hmhalf : m < 1/2 := (hmv false).trans_lt (hv false).2
  have hρ : 0 < δ*m := mul_pos hδ hm
  have hρr : δ*m < r := by nlinarith
  obtain ⟨a₀,ha₀,ha₀small,havoid⟩ := exists_band_width_avoiding_lateralRemainder
    U hρ hρr hr1 side hF hcenter
  let a := min a₀ m
  have ha : 0 < a := lt_min ha₀ hm
  have ham : a ≤ m := min_le_right _ _
  have haa₀ : a ≤ a₀ := min_le_left _ _
  have hasmall : a ≤ 1/2 := haa₀.trans ha₀small
  have hav (b : Bool) : a ≤ v b := ham.trans (hmv b)
  have hsource {z : V2} (hz : z ∈ Rim) {s : ℝ} (hs : s ∈ Icc (-a) a) :
      (z,s) ∈ Rim ×ˢ I := ⟨hz,by constructor <;> linarith [hs.1,hs.2]⟩
  have hformula (b : Bool) (t : ℝ) (ht : t ∈ J) (s : ℝ) (hs : s ∈ Icc (-a) a) :
      F (rimArm b t,s)=prescribedArmBand U r δ t₀ t₁ side b (sign (o b)*(s/2),t) := by
    have hbound : s/2 ∈ Icc (-(v b)) (v b) := by
      constructor <;> linarith [hs.1,hs.2,hav b,hv b |>.1]
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      full_arm_formula harms b ht hbound
  refine ⟨a,ha,hasmall,hav,?_,hformula⟩
  intro z hz s hs
  constructor
  · intro hy
    have hnot : F (z,s) ∉ U.map '' lateralRemainder r (δ*m) side :=
      havoid ⟨hz,⟨by linarith [hs.1],by linarith [hs.2]⟩⟩
    have hband : F (z,s) ∈ ⋃ b : Bool, U.map '' openBand r (δ*m) (selectedCorner side b) := by
      by_contra hh
      apply hnot
      rw [original_lateralRemainder_eq_sdiff U hρ hρr hr1 side]
      exact ⟨hy,hh⟩
    obtain ⟨b,hb⟩ := mem_iUnion.mp hband
    obtain ⟨p,hp,hpF⟩ := openBand_subset_full_arm_image U hδ hm (by linarith)
      horder side b (hmv b) (hv b).2 harms hb
    have hpBand : p ∈ Rim ×ˢ I := by
      obtain ⟨t,ht,hval⟩ := hp.1
      exact ⟨hval ▸ rimArm_mem ht,hp.2⟩
    have heq : p=(z,s) := hi hpBand (hsource hz hs) hpF
    obtain ⟨t,ht,hval⟩ := hp.1
    exact ⟨b,t,ht,(congrArg Prod.fst heq).symm.trans hval.symm⟩
  · rintro ⟨b,t,ht,rfl⟩
    rw [hformula b t ht s hs]
    apply prescribedArmBand_mem_lateral U hδ hδr horder side b
    refine ⟨?_,ht⟩
    cases o b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,mem_Icc]
    all_goals constructor <;> linarith [hs.1,hs.2]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
