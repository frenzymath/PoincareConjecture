import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.FullBand
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.PhysicalPatches
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.Pasting

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_full_band_of_actual_arm_lifts
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e Q j)
    (hopen : IsOpen ((Subtype.val : frontier Q → X) ⁻¹'
      (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)))))
    (arms : Bool → P2 → X) (L : ∀ b, IntervalBandLift P (arms b) (rimArm b)) :
    ∃ (orientation : Bool → Bool) (v : Bool → ℝ) (F : E → X),
      (∀ b, 0 < v b ∧ v b < 1/2 ∧ v b ≤ (L b).width) ∧
      PolyhedralPLInCharts e F (Rim ×ˢ I) ∧ InjOn F (Rim ×ˢ I) ∧
      MapsTo F (Rim ×ˢ I) (frontier Q) ∧ (∀ z ∈ Rim, F (z,0)=j z) ∧
      IsOpen ((Subtype.val : frontier Q → X) ⁻¹' (F '' (Rim ×ˢ Ioo (-1 : ℝ) 1))) ∧
      (∀ b a t, t ∈ J → ∀ u ∈ Icc (0 : ℝ) (v b),
        F (rimArm b t,2 * (sign a*u)) = arms b (sign (orientation b)*(sign a*u),t)) := by
  classical
  choose o v hv hvs hvL H hH hfix hphysical using fun b => (L b).exists_signed_arm_patches
  obtain ⟨G,hG,hchart,hfixed⟩ := exists_rimCylinder_homeomorph
    (fun i => H i.1 i.2) (fun i => hH i.1 i.2) (fun i => hfix i.1 i.2)
  obtain ⟨F,hF,hFi,hFQ,hFc,hFo,hformula⟩ :=
    exists_full_original_band_of_cylinder_correction P hopen G hG
      (fun z hz => hfixed ⟨(z,0),hz,by norm_num⟩ (Or.inl rfl))
      (fun p hp => hfixed p (Or.inr hp))
  refine ⟨o,v,F,fun b => ⟨hv b,hvs b,hvL b⟩,hF,hFi,hFQ,hFc,hFo,?_⟩
  intro b a t ht u hu
  have hp : (t,u) ∈ halfArmRectangle :=
    ⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,hu.1,hu.2.trans (hvs b).le⟩
  have hB : (rimArm b t,2*(sign a*u)) ∈ Rim ×ˢ I := by
    refine ⟨rimArm_mem ht,?_⟩
    cases a <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,mem_Icc]
    all_goals constructor <;> linarith [hu.1,hu.2,hvs b]
  have hsource : halfBandScale (rimArm b t,2*(sign a*u)) = halfArmChart (b,a) (t,u) := by
    simp only [halfBandScale_apply,halfArmChart,armPoint_eq_rimArm b ht]
    congr 1
    ring
  rw [hformula _ hB]
  change P.map (G (⟨halfBandScale (rimArm b t,2*(sign a*u)),
    halfBandScale_mem.mpr hB⟩ : rimCylinder)) = _
  have hscaled :
      (⟨halfBandScale (rimArm b t,2*(sign a*u)),halfBandScale_mem.mpr hB⟩ : rimCylinder) =
      ⟨halfArmChart (b,a) (t,u),halfArmCarrier_cover ▸
        mem_iUnion.mpr ⟨(b,a),mem_image_of_mem (halfArmChart (b,a)) hp⟩⟩ :=
    Subtype.ext hsource
  rw [hscaled]
  exact (congrArg P.map (hchart (b,a) ⟨(t,u),hp⟩)).trans
    (hphysical b a ⟨(t,u),hp⟩ ⟨ht,hu⟩)

theorem exists_full_complement_disk_band
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) {r δ t₀ t₁ : ℝ}
    (hδ : 0 < δ) (hδr : δ < r) (hr1 : r < 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (j : Bool) {k : P2 → X}
    (hk : PolyhedralPLInCharts e k (J ×ˢ J))
    (hki : IsEmbedding (fun p : J ×ˢ J => k p))
    (hkQ : MapsTo k (J ×ˢ J) (R \ U.map '' TubeExterior.openTube r))
    (hkproper : ∀ p ∈ J ×ˢ J,
      k p ∈ frontier (R \ U.map '' TubeExterior.openTube r) ↔ p ∈ frontier (J ×ˢ J))
    (himage : k '' (J ×ˢ J) =
      (if j then f₁ '' T else f₀ '' S) ∩ (R \ U.map '' TubeExterior.openTube r))
    (hleft : ∀ t ∈ J, k (0,t) = originalBandMap U r (true,if j then false else true)
      (0,(1-t)*t₀+t*t₁))
    (hright : ∀ t ∈ J, k (1,t) = originalBandMap U r (false,if j then true else false)
      (0,(1-t)*t₀+t*t₁)) :
    ∃ (orientation : Bool → Bool) (v : Bool → ℝ) (F : E → X),
      (∀ b, 0 < v b ∧ v b < 1/2) ∧
      PolyhedralPLInCharts e F (Rim ×ˢ I) ∧ InjOn F (Rim ×ˢ I) ∧
      MapsTo F (Rim ×ˢ I) (frontier (R \ U.map '' TubeExterior.openTube r)) ∧
      (∀ z ∈ Rim, F (z,0)=(k ∘ CubeCoordinates.toRectangle) z) ∧
      IsOpen ((Subtype.val : frontier (R \ U.map '' TubeExterior.openTube r) → X) ⁻¹'
        (F '' (Rim ×ˢ Ioo (-1 : ℝ) 1))) ∧
      (∀ b a t, t ∈ J → ∀ u ∈ Icc (0 : ℝ) (v b),
        F (rimArm b t,2 * (sign a*u)) =
          prescribedArmBand U r δ t₀ t₁ j b (sign (orientation b)*(sign a*u),t)) := by
  classical
  obtain ⟨P,hopen,hL⟩ := exists_original_disk_collar_with_arm_lifts
    U hR he hδ hδr hr1 horder j hk hki hkQ hkproper himage hleft hright
  let L b := Classical.choice (hL b)
  obtain ⟨o,v,F,hv,hF,hFi,hFQ,hFc,hFo,hFa⟩ := exists_full_band_of_actual_arm_lifts P
    (hopen (1/2) (by norm_num) (by norm_num)).2
    (prescribedArmBand U r δ t₀ t₁ j) L
  exact ⟨o,v,F,fun b => ⟨(hv b).1,(hv b).2.1⟩,hF,hFi,hFQ,hFc,hFo,hFa⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
