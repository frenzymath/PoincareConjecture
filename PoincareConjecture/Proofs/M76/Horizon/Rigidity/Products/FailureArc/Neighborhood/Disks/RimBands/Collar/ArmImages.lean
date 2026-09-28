import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.LateralControl



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

theorem full_arm_formula {X : Type*} {F : E → X} {arms : Bool → P2 → X}
    {o : Bool → Bool} {v : Bool → ℝ}
    (h : ∀ b a t, t ∈ J → ∀ u ∈ Icc (0 : ℝ) (v b),
      F (rimArm b t,2*(sign a*u))=arms b (sign (o b)*(sign a*u),t))
    (b : Bool) {t s : ℝ} (ht : t ∈ J) (hs : s ∈ Icc (-(v b)) (v b)) :
    F (rimArm b t,2*s)=arms b (sign (o b)*s,t) := by
  rcases le_total 0 s with h0 | h0
  · simpa [sign] using h b false t ht s ⟨h0,hs.2⟩
  · simpa [sign] using h b true t ht (-s) ⟨by linarith,by linarith [hs.1]⟩

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem prescribedArmBand_mem_lateral
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ t₀ t₁ : ℝ} (hδ : 0 < δ) (hδr : δ < r)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (side b : Bool)
    {p : P2} (hp : p ∈ parameter 1) :
    prescribedArmBand U r δ t₀ t₁ side b p ∈ U.map '' lateral r := by
  refine ⟨bandMap r (selectedCorner side b) (armCoordinates δ t₀ t₁ b p),?_,rfl⟩
  apply band_subset_lateral hδ.le hδr.le (selectedCorner side b)
  apply (bandMap_image hδ.le (selectedCorner side b)).subset
  exact ⟨_,(armCoordinates_bijOn hδ horder b).1 hp,rfl⟩

theorem openBand_subset_full_arm_image
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ t₀ t₁ m : ℝ} (hδ : 0 < δ) (hm : 0 < m) (hm1 : m ≤ 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (side b : Bool)
    {F : E → X} {o : Bool → Bool} {v : Bool → ℝ} (hmv : m ≤ v b)
    (hvs : v b < 1/2)
    (h : ∀ b a t, t ∈ J → ∀ u ∈ Icc (0 : ℝ) (v b),
      F (rimArm b t,2*(sign a*u))=
        prescribedArmBand U r δ t₀ t₁ side b (sign (o b)*(sign a*u),t)) :
    U.map '' openBand r (δ*m) (selectedCorner side b) ⊆
      F '' ((rimArm b '' J) ×ˢ I) := by
  rintro y ⟨z,hz,rfl⟩
  obtain ⟨q,hq,rfl⟩ := (bandMap_open_image (mul_pos hδ hm).le _).symm.subset hz
  have hqδ : q ∈ parameter δ := by
    refine ⟨?_,hq.2⟩
    constructor <;> nlinarith [hq.1.1,hq.1.2]
  obtain ⟨p,hp,hpq⟩ := (armCoordinates_bijOn hδ horder b).2.2 hqδ
  have hpbound : p.1 ∈ Icc (-m) m := by
    have heq := congrArg Prod.fst hpq
    rw [armCoordinates_apply] at heq
    cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul] at heq
    all_goals constructor <;> nlinarith [hq.1.1,hq.1.2]
  have hs : sign (o b)*p.1 ∈ Icc (-(v b)) (v b) := by
    cases o b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    all_goals constructor <;> linarith [hpbound.1,hpbound.2]
  have hsI : 2*(sign (o b)*p.1) ∈ I := by
    constructor <;> linarith [hs.1,hs.2]
  refine ⟨(rimArm b p.2,2*(sign (o b)*p.1)),⟨⟨p.2,hp.2,rfl⟩,hsI⟩,?_⟩
  rw [full_arm_formula h b hp.2 hs,sign_mul_sign]
  change U.map (bandMap r (selectedCorner side b) (armCoordinates δ t₀ t₁ b p)) = _
  rw [hpq]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
