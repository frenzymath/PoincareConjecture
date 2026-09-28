import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.CapSides
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "H" => Icc (-(1/2 : ℝ)) (1/2)
local notation "Rect" => (I ×ˢ I : Set P2)

def stripBase : Set P2 := I ×ˢ H

def exchangeDepth : C3 →ᴬ[ℝ] C3 :=
  let a := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.comp
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap
  let s := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap.comp
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap
  (a.prod (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap).prod s

@[simp] theorem exchangeDepth_apply (p : C3) : exchangeDepth p = ((p.1.1,p.2),p.1.2) := rfl

def stripCoordinates (p : C3) : V2 × ℝ :=
  (CubeCoordinates.fromRectangle (p.1.1,p.2),p.1.2)

theorem stripCoordinates_finitePL :
    FinitePiecewiseAffineOn stripCoordinates (stripBase ×ˢ I) := by
  have hH := isFinitePLBallPair_Icc (by norm_num : -(1/2 : ℝ) < 1/2)
  have hH' := hH
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hH'
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) H :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have hprod := CubeCoordinates.fromRectangle_finitePL.prodMap hid
  have hball := ((isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod hH).prod
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hball
  have hswap : FinitePiecewiseAffineOn exchangeDepth (stripBase ×ˢ I) :=
    ⟨L,hL,hLs,L.affineOnFaces_affine exchangeDepth⟩
  exact hprod.comp hswap (fun p hp => ⟨⟨hp.1.1,hp.2⟩,hp.1.2⟩)

theorem stripCoordinates_bijOn : BijOn stripCoordinates (stripBase ×ˢ I) (Disk ×ˢ H) := by
  have hmem (p : C3) (hp : p ∈ stripBase ×ˢ I) : stripCoordinates p ∈ Disk ×ˢ H := by
    refine ⟨(CubeCoordinates.toRectangle_mem_iff _).mp ?_,hp.1.2⟩
    simpa only [stripCoordinates,CubeCoordinates.toRectangle_fromRectangle] using
      (show (p.1.1,p.2) ∈ Rect from ⟨hp.1.1,hp.2⟩)
  refine ⟨hmem,?_,?_⟩
  · intro p hp q hq h
    have ha := congrArg (fun z : V2 × ℝ => CubeCoordinates.toRectangle z.1) h
    have hs := congrArg Prod.snd h
    simp only [stripCoordinates,CubeCoordinates.toRectangle_fromRectangle] at ha hs
    have hx := congrArg (fun z : P2 => z.1) ha
    have ht := congrArg (fun z : P2 => z.2) ha
    exact Prod.ext (Prod.ext hx hs) ht
  · rintro ⟨z,s⟩ ⟨hz,hs⟩
    have ht := CubeCoordinates.toRectangle_bijOn.1 hz
    exact ⟨(((CubeCoordinates.toRectangle z).1,s),(CubeCoordinates.toRectangle z).2),
      ⟨⟨ht.1,hs⟩,ht.2⟩,by
        change (CubeCoordinates.fromRectangle (CubeCoordinates.toRectangle z),s) = (z,s)
        rw [CubeCoordinates.fromRectangle_toRectangle]⟩

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}

def diskStrip (P : OriginalDiskProduct e Q j) : C3 → X := P.map ∘ stripCoordinates

theorem diskStrip_properties (P : OriginalDiskProduct e Q j) :
    PolyhedralPLInCharts e (diskStrip P) (stripBase ×ˢ I) ∧
      IsEmbedding (fun p : stripBase ×ˢ I => diskStrip P p) ∧
      MapsTo (diskStrip P) (stripBase ×ˢ I) Q ∧
      diskStrip P '' (stripBase ×ˢ I) = P.closedStrip := by
  have hmap : MapsTo stripCoordinates (stripBase ×ˢ I) (Disk ×ˢ Icc (-1 : ℝ) 1) := by
    intro p hp
    have h := stripCoordinates_bijOn.1 hp
    exact ⟨h.1,by linarith [h.2.1],by linarith [h.2.2]⟩
  have hF := stripCoordinates_finitePL
  obtain ⟨K,hK,hKs,_⟩ := hF
  have hPL : PolyhedralPLInCharts e (diskStrip P) (stripBase ×ˢ I) :=
    hKs ▸ P.polyhedral.comp_finitePiecewiseAffineOn K hK
      (hKs.symm ▸ stripCoordinates_finitePL) (fun p hp => hmap (hKs.subset hp))
  have hinj : InjOn (diskStrip P) (stripBase ×ˢ I) := fun _ hp _ hq h =>
    stripCoordinates_bijOn.2.1 hp hq (P.injective (hmap hp) (hmap hq) h)
  let : CompactSpace (stripBase ×ˢ I) :=
    isCompact_iff_compactSpace.mp ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  refine ⟨hPL,(hPL.continuousOn.domRestrict.isClosedEmbedding
    (fun p q h => Subtype.ext (hinj p.property q.property h))).isEmbedding,
    fun p hp => P.inside (hmap hp),?_⟩
  change (P.map ∘ stripCoordinates) '' _ = _
  rw [image_comp,stripCoordinates_bijOn.image_eq]
  rfl

omit [T2Space X] in
theorem diskStrip_cap (P : OriginalDiskProduct e Q j) (x s t : ℝ) :
    diskStrip P ((x,s),t) = capRectangle P s (x,t) := rfl

omit [T2Space X] in
theorem diskStrip_arm (P : OriginalDiskProduct e Q j) (b : Bool) (s t : ℝ) :
    diskStrip P ((if b then 0 else 1,s),t) = P.map (rimArmPoint b t,s) := by
  exact capRectangle_arm_parameter P s b t

omit [T2Space X] in
theorem diskStrip_depth_face (P : OriginalDiskProduct e Q j) (x s t : ℝ) :
    diskStrip P ((x,s),t) = P.map (![2*x-1,2*t-1],s) := rfl

omit [T2Space X] in
theorem diskStrip_depth_image (P : OriginalDiskProduct e Q j) {t : ℝ} (ht : t ∈ I) :
    diskStrip P '' (stripBase ×ˢ {t}) =
      P.map '' ((Disk ∩ {z | z 1 = 2*t-1}) ×ˢ H) := by
  apply Subset.antisymm
  · rintro _ ⟨p,⟨hp,hpt⟩,rfl⟩
    have hpt' : p.2 = t := hpt
    refine ⟨stripCoordinates p,⟨⟨?_,?_⟩,hp.2⟩,rfl⟩
    · exact (stripCoordinates_bijOn.1 ⟨hp,hpt'.symm ▸ ht⟩).1
    · simp [stripCoordinates,CubeCoordinates.fromRectangle,hpt']
  · rintro _ ⟨⟨z,s⟩,⟨⟨hz,hzt⟩,hs⟩,rfl⟩
    have hrect := CubeCoordinates.toRectangle_bijOn.1 hz
    have hdepth : (CubeCoordinates.toRectangle z).2 = t :=
      ((CubeCoordinates.toRectangle_side_coordinates z t).2).mpr hzt
    refine ⟨(((CubeCoordinates.toRectangle z).1,s),t),⟨⟨hrect.1,hs⟩,rfl⟩,?_⟩
    change P.map (CubeCoordinates.fromRectangle ((CubeCoordinates.toRectangle z).1,t),s) = _
    rw [← hdepth,CubeCoordinates.fromRectangle_toRectangle]

theorem diskStrip_end_in_frontier (P : OriginalDiskProduct e Q j)
    {p : P2} (hp : p ∈ stripBase) {t : ℝ} (ht : t = 0 ∨ t = 1) :
    diskStrip P (p,t) ∈ frontier Q := by
  have htI : t ∈ I := by rcases ht with rfl|rfl <;> norm_num
  have hs : p.2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
  have hfront : (p.1,t) ∈ frontier Rect := by
    rw [frontier_prod_eq,isClosed_Icc.closure_eq,frontier_Icc zero_le_one]
    exact Or.inl ⟨hp.1,by simpa only [mem_insert_iff,mem_singleton_iff] using ht⟩
  exact ((capRectangle_properties P hs).2.2.2.2 (p.1,t) ⟨hp.1,htI⟩).mpr hfront

omit [T2Space X] in
theorem diskStrip_prescribed_arms
    {R W : Set X} {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (P : OriginalDiskProduct e Q j) (F : V2 × ℝ → X)
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r : ℝ) (side : Bool) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 < w)
    (hwρ : w/ρ ≤ 1)
    (hmark : ∀ z ∈ sphere (0 : V2) 1, ∀ s ∈ Icc (-1 : ℝ) 1,
      P.map (z,s) = F (z,(w/ρ)*s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ Icc (-1 : ℝ) 1,
      F (rimArmPoint b t,s) = RimBands.prescribedArmBand U r ρ 0 1 side b (s,t)) :
    ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ H,
      diskStrip P ((if b then 0 else 1,s),t) =
        TubeExterior.CornerBands.originalBandMap U r (b,if side then !b else b)
          (w*(TubeExterior.CornerBands.sign b*s),t) := by
  intro b t ht s hs
  exact capRectangle_common_width_arm_edges P F U r side hρ hw hwρ hmark harms b t ht s
    ⟨by linarith [hs.1],by linarith [hs.2]⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
