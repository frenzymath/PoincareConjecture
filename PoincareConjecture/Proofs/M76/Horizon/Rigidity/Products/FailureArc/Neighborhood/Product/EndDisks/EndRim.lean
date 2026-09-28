import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.EndComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PanelCylinderPeriod



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open BoundaryAssembly ProductPieces AnnularParameter

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_original_panel_end_rim
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip)
    (t : ℝ) (ht : t = 0 ∨ t = 1) :
    ∃ c : V2 → X,
      ∃ γ : C(Rim, connectedComponentIn (frontier R) (U.map ((0,0),t))),
      PolyhedralPLInCharts e c Rim ∧ InjOn c Rim ∧ Function.Injective γ ∧
      (∀ z, (γ z : X) = c z) ∧
      c '' Rim = ⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {t}) := by
  obtain ⟨b,hb,hbi,_,_,hbslice⟩ := exists_marked_panel_cylinder_with_period U hR he
    hw hr1 P F ρ hρ hρr hwρ hmark harms hlateral hdis
  have htI : t ∈ I := by rcases ht with rfl | rfl <;> norm_num
  let a : V2 →ᴬ[ℝ] V2 × ℝ :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 t)
  let c : V2 → X := b ∘ a
  have haimage : a '' Rim = Rim ×ˢ {t} := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hx,rfl⟩
    · rintro ⟨hz,htz⟩
      refine ⟨z.1,hz,?_⟩
      exact Prod.ext rfl (show t = z.2 from htz.symm)
  have hc : PolyhedralPLInCharts e c Rim := by
    obtain ⟨K,hK,hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
    have ha : FinitePiecewiseAffineOn a K.space :=
      ⟨K,hK,rfl,K.affineOnFaces_affine a⟩
    exact hKs ▸ hb.comp_finitePiecewiseAffineOn K hK ha
      (fun x hx => ⟨hKs.subset hx,htI⟩)
  have hci : InjOn c Rim := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hbi ⟨hx,htI⟩ ⟨hy,htI⟩ hxy)
  have hcimage : c '' Rim =
      ⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {t}) := by
    change (b ∘ a) '' Rim = _
    rw [image_comp,haimage,hbslice t htI]
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  have hmaps : MapsTo c Rim (connectedComponentIn (frontier R) (U.map ((0,0),t))) := by
    intro z hz
    exact panel_rim_subset_component U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark harms hlateral hwr t ht (hcimage.subset (mem_image_of_mem c hz))
  let γ : C(Rim, connectedComponentIn (frontier R) (U.map ((0,0),t))) :=
    ⟨fun z => ⟨c z,hmaps z.property⟩,hc.continuousOn.domRestrict.subtype_mk _⟩
  refine ⟨c,γ,hc,hci,?_,fun _ => rfl,hcimage⟩
  intro z y hzy
  exact Subtype.ext (hci z.property y.property (congrArg Subtype.val hzy))

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
