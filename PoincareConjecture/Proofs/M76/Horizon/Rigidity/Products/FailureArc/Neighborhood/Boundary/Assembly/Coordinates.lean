import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CapRectangles
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.PanelMaps



set_option autoImplicit false
noncomputable section
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

def panelCoordinates (r δ : ℝ) (reverse : Bool) : P2 →ᴬ[ℝ] P2 :=
  ((sign reverse*(r-δ)) •
    ((2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ P2 1)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

theorem panelCoordinates_apply (r δ : ℝ) (b : Bool) (p : P2) :
    panelCoordinates r δ b p = (sign b*((r-δ)*(2*p.1-1)),p.2) := by
  apply Prod.ext
  · change (sign b*(r-δ))*(2*p.1-1) = _
    ring
  · rfl

theorem panelCoordinates_bijOn {r δ : ℝ} (hδr : δ < r) (b : Bool) :
    BijOn (panelCoordinates r δ b) Rect (panelParameter r δ) := by
  have ha : 0 < r-δ := sub_pos.mpr hδr
  refine ⟨?_,?_,?_⟩
  · intro p hp
    rw [panelCoordinates_apply]
    refine ⟨?_,hp.2⟩
    cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    all_goals constructor <;> nlinarith [hp.1.1,hp.1.2]
  · intro p hp q hq h
    rw [panelCoordinates_apply,panelCoordinates_apply] at h
    have ht := congrArg Prod.snd h
    have hx := congrArg (fun z : P2 => sign b*z.1) h
    simp only [sign_mul_sign] at hx
    have hx' := mul_left_cancel₀ ha.ne' hx
    exact Prod.ext (by linarith) ht
  · intro p hp
    let x := (sign b*p.1/(r-δ)+1)/2
    have hsign : -(r-δ) ≤ sign b*p.1 ∧ sign b*p.1 ≤ r-δ := by
      cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
      all_goals constructor <;> linarith [hp.1.1,hp.1.2]
    have hquot : -1 ≤ sign b*p.1/(r-δ) ∧ sign b*p.1/(r-δ) ≤ 1 := by
      exact ⟨(le_div_iff₀ ha).mpr (by linarith [hsign.1]),
        (div_le_iff₀ ha).mpr (by linarith [hsign.2])⟩
    refine ⟨(x,p.2),⟨⟨by dsimp [x]; linarith [hquot.1],
      by dsimp [x]; linarith [hquot.2]⟩,hp.2⟩,?_⟩
    rw [panelCoordinates_apply]
    apply Prod.ext
    · change sign b*((r-δ)*(2*x-1)) = p.1
      have hx : 2*x-1 = sign b*p.1/(r-δ) := by dsimp [x]; ring
      rw [hx,mul_div_cancel₀ _ ha.ne',sign_mul_sign]
    · rfl

theorem panelCoordinates_finitePL (r δ : ℝ) (b : Bool) :
    FinitePiecewiseAffineOn (panelCoordinates r δ b) Rect := by
  obtain ⟨K,hK,hKs,_⟩ := CubeCoordinates.fromRectangle_finitePL
  exact ⟨K,hK,hKs,K.affineOnFaces_affine (panelCoordinates r δ b)⟩

def rectangleReflection : P2 →ᴬ[ℝ] P2 :=
  (ContinuousAffineMap.const ℝ P2 1 -
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

@[simp] theorem rectangleReflection_apply (p : P2) :
    rectangleReflection p = (1-p.1,p.2) := rfl

theorem rectangleReflection_bijOn : BijOn rectangleReflection Rect Rect := by
  have hmap : MapsTo rectangleReflection Rect Rect := by
    intro p hp
    exact ⟨⟨by change 0 ≤ 1-p.1; linarith [hp.1.2],
      by change 1-p.1 ≤ 1; linarith [hp.1.1]⟩,hp.2⟩
  have hinv (p : P2) : rectangleReflection (rectangleReflection p) = p := by
    simp
  exact ⟨hmap,fun p _ q _ h => by
    simpa only [hinv] using congrArg rectangleReflection h,
    fun p hp => ⟨rectangleReflection p,hmap hp,hinv p⟩⟩

theorem rectangleReflection_finitePL : FinitePiecewiseAffineOn rectangleReflection Rect := by
  obtain ⟨K,hK,hKs,_⟩ := CubeCoordinates.fromRectangle_finitePL
  exact ⟨K,hK,hKs,K.affineOnFaces_affine rectangleReflection⟩

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem reflected_rectangle_properties {f : P2 → X}
    (hf : PolyhedralPLInCharts e f Rect) (hi : InjOn f Rect) :
    PolyhedralPLInCharts e (f ∘ rectangleReflection) Rect ∧
      InjOn (f ∘ rectangleReflection) Rect ∧
      (f ∘ rectangleReflection) '' Rect = f '' Rect := by
  have hbij := rectangleReflection_bijOn
  obtain ⟨K,hK,hKs,_⟩ := rectangleReflection_finitePL
  refine ⟨?_,hi.comp hbij.2.1 hbij.1,?_⟩
  · exact hKs ▸ hf.comp_finitePiecewiseAffineOn K hK
      (hKs.symm ▸ rectangleReflection_finitePL) (fun p hp => hbij.1 (hKs.subset hp))
  · rw [image_comp,hbij.image_eq]

def unitPanelMap (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r δ : ℝ) (i : Bool × Bool) (reverse : Bool) : P2 → X :=
  originalPanelMap U r i ∘ panelCoordinates r δ reverse

theorem unitPanelMap_properties (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1)
    (i : Bool × Bool) (b : Bool) :
    PolyhedralPLInCharts e (unitPanelMap U r δ i b) Rect ∧
      IsEmbedding (fun p : Rect => unitPanelMap U r δ i b p) ∧
      unitPanelMap U r δ i b '' Rect = U.map '' panel r δ i ∧
      ∀ p ∈ Rect, unitPanelMap U r δ i b p ∈ frontier R ↔ p.2=0 ∨ p.2=1 := by
  obtain ⟨hP,hPi,_,_,hfront,himage⟩ := originalPanelMap_properties U hR he hδ hδr hr1 i
  have hbij := panelCoordinates_bijOn hδr b
  have hc := panelCoordinates_finitePL r δ b
  have hc' := hc
  obtain ⟨K,hK,hKs,_⟩ := hc'
  have hPL : PolyhedralPLInCharts e (unitPanelMap U r δ i b) Rect :=
    hKs ▸ hP.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hc)
      (fun p hp => hbij.1 (hKs.subset hp))
  let : CompactSpace Rect := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  refine ⟨hPL,?_,?_,?_⟩
  · apply (hPL.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro p q hpq
    have heq := congrArg Subtype.val (hPi.injective
      (a₁ := ⟨_,hbij.1 p.property⟩) (a₂ := ⟨_,hbij.1 q.property⟩) hpq)
    exact Subtype.ext (hbij.2.1 p.property q.property heq)
  · change (_ ∘ _) '' _ = _
    rw [image_comp,hbij.image_eq,himage]
  · intro p hp
    exact hfront _ (hbij.1 hp)

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
