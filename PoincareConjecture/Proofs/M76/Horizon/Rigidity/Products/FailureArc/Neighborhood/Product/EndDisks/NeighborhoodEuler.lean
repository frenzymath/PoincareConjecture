import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodEulerValuation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodEulerLifts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.EndComponents
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages



set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open ProductPieces TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Half" => Icc (-(1 / 2 : ℝ)) (1 / 2)

private theorem pieceBase_ballPair {r : ℝ} (hr : 0 < r) (i : Option Bool) :
    ∃ q, IsFinitePLBallPair P2 (pieceBase r i) q := by
  cases i with
  | none => exact ⟨_, (isFinitePLBallPair_Icc (show -r < r by linarith)).prod
      (isFinitePLBallPair_Icc (show -r < r by linarith))⟩
  | some b => exact ⟨_, (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show -(1 / 2 : ℝ) < 1 / 2 by norm_num))⟩

private def stripEndEdge (b : Bool) : Set P2 := {if b then 0 else 1} ×ˢ Half

private theorem stripEndEdge_subset (b : Bool) : stripEndEdge b ⊆ stripBase := by
  rintro x ⟨hx,hs⟩
  have hx' : x.1 = if b then 0 else 1 := hx
  exact ⟨by rw [hx']; cases b <;> norm_num,hs⟩

private theorem stripEndEdge_ballPair (b : Bool) :
    ∃ q, IsFinitePLBallPair ℝ (stripEndEdge b) q := by
  let f : ℝ →ᴬ[ℝ] P2 := (ContinuousAffineMap.const ℝ ℝ (if b then 0 else 1)).prod
    (ContinuousAffineMap.id ℝ ℝ)
  have hf : InjOn f Half := fun x _ y _ heq => congrArg Prod.snd heq
  have him : f '' Half = stripEndEdge b := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨rfl,hs⟩
    · rintro ⟨hx,hs⟩
      exact ⟨x.2,hs,Prod.ext hx.symm rfl⟩
  exact ⟨_,him ▸ (isFinitePLBallPair_Icc (show -(1 / 2 : ℝ) < 1 / 2 by norm_num)).affine_image f hf⟩

theorem exists_original_endpoint_neighborhood_euler_model
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w / ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w / ρ b) * s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip)
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (H : K.space ≃ₜ connectedComponentIn (frontier R) (U.map ((0,0),t)))
    (a : E → X) (ha : PolyhedralPLInCharts e a K.space)
    (haval : ∀ x : K.space, a x = (H x : X)) :
    ∃ L N : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧ N ≤ L ∧
      N.space = K.space ∩ a ⁻¹' (⋃ i, range (fun z => pieceParameter U P r i (z,t))) ∧
      (∀ s ∈ N.faces, s.card ≤ 3) ∧ N.surfaceEulerCount = -1 := by
  classical
  have hr : 0 < r := (hρ false).trans (hρr false)
  let A : Set X := ⋃ i, range (fun z => pieceParameter U P r i (z,t))
  have hAS := closed_longitudinal_slice_subset_component U hR he hw hr1 P F ρ hρ hρr hwρ
    hmark harms hlateral t ht
  choose rim hrim using fun i => pieceBase_ballPair hr i
  choose B q hB hBs hq hqs using fun i => (hrim i).exists_finite_carrier_and_rim_complexes
  let f : Option Bool → P2 → X := fun i x => pieceMap U P i (x,t)
  have hpl (i : Option Bool) : PolyhedralPLInCharts e (pieceMap U P i) (pieceBase r i ×ˢ I) := by
    cases i with
    | none => exact (tubePiece_properties U hr hr1).1
    | some b => exact (diskStrip_properties (P b)).1
  have hfulli (i : Option Bool) : InjOn (pieceMap U P i) (pieceBase r i ×ˢ I) := by
    cases i with
    | none => exact (TubeExterior.OriginalIntervalTube.restrict_closedTube U hr hr1).2.1
    | some b =>
      intro x hx y hy hxy
      exact congrArg Subtype.val ((diskStrip_properties (P b)).2.1.injective
        (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have hf (i : Option Bool) : PolyhedralPLInCharts e (f i) (B i).space := by
    let ins : P2 →ᴬ[ℝ] (P2 × ℝ) := (ContinuousAffineMap.id ℝ P2).prod
      (ContinuousAffineMap.const ℝ P2 (t : ℝ))
    exact (hpl i).comp_finitePiecewiseAffineOn (B i) (hB i)
      ((B i).affineOnFaces_affine ins |>.finitePiecewiseAffineOn (hB i))
      (fun x hx => ⟨(hBs i).subset hx,t.property⟩)
  have hfi (i : Option Bool) : InjOn (f i) (B i).space := fun x hx y hy hxy =>
    congrArg Prod.fst (hfulli i ⟨(hBs i).subset hx,t.property⟩
      ⟨(hBs i).subset hy,t.property⟩ hxy)
  have hfS (i : Option Bool) : MapsTo (f i) (B i).space
      (connectedComponentIn (frontier R) (U.map ((0,0),t))) := by
    intro x hx
    exact hAS (mem_iUnion.mpr ⟨i,⟨⟨x,(hBs i).subset hx⟩,rfl⟩⟩)
  choose g hg hgi hgK hgv using fun i => exists_finitePL_lift_of_original_embedding
    hcompat K H a ha haval (B i) (hB i) (f i) (hf i) (hfi i) (hfS i)
  have hg' (i : Option Bool) : FinitePiecewiseAffineOn (g i) (pieceBase r i) := hBs i ▸ hg i
  have hgi' (i : Option Bool) : InjOn (g i) (pieceBase r i) := hBs i ▸ hgi i
  have hgK' (i : Option Bool) : MapsTo (g i) (pieceBase r i) K.space := hBs i ▸ hgK i
  have hgv' (i : Option Bool) (x : P2) (hx : x ∈ pieceBase r i) :
      a (g i x) = pieceMap U P i (x,t) := hgv i x ((hBs i).symm.subset hx)
  have hai : InjOn a K.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((haval ⟨x,hx⟩).symm.trans (hxy.trans (haval ⟨y,hy⟩)))))
  let M (i : Option Bool) := g i '' pieceBase r i
  let m (i : Option Bool) := g i '' rim i
  have hM (i : Option Bool) : IsFinitePLBallPair P2 (M i) (m i) :=
    (hrim i).image (hg' i) (hgi' i)
  choose edgeRim hedge using stripEndEdge_ballPair
  let L (side b : Bool) := g (some side) '' stripEndEdge b
  let l (side b : Bool) := g (some side) '' edgeRim b
  have hL (side b : Bool) : IsFinitePLBallPair ℝ (L side b) (l side b) :=
    (hedge b).image_of_subset (hg' (some side)) (stripEndEdge_subset b) (hgi' (some side))
  have hcontact (side : Bool) : M none ∩ M (some side) = L side false ∪ L side true := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,p,hp,hpz⟩
      have heq : U.map (z,t) = diskStrip (P side) (p,t) :=
        (hgv' none z hz).symm.trans ((congrArg a hpz.symm).trans (hgv' (some side) p hp))
      obtain ⟨b,hb⟩ := (diskStrip_mem_closedTube_iff U hR he hr hr1
        (div_pos hw (hρ side)) (hwρ side) (P side) (F side) (hmark side)
        (hlateral side) hp t.property).mp ⟨(z,t),⟨hz,t.property⟩,heq⟩
      have hm : g none z ∈ L side b := ⟨p,⟨hb,hp.2⟩,hpz⟩
      cases b
      · exact Or.inl hm
      · exact Or.inr hm
    · intro x hx
      have hex : ∃ b, x ∈ L side b := by
        rcases hx with hx | hx
        · exact ⟨false,hx⟩
        · exact ⟨true,hx⟩
      obtain ⟨b,p,hp,rfl⟩ := hex
      have hpS := stripEndEdge_subset b hp
      have hm := (diskStrip_mem_closedTube_iff U hR he hr hr1
        (div_pos hw (hρ side)) (hwρ side) (P side) (F side) (hmark side)
        (hlateral side) hpS t.property).mpr ⟨b,hp.1⟩
      obtain ⟨⟨z,s⟩,⟨hz,hs⟩,heq⟩ := hm
      have hst := ((tube_diskStrip_eq_iff U hR he (hρ side) (hρr side) hr1 hw (hwρ side)
        (P side) (F side) side (hmark side) (harms side) (hlateral side)
        hz hpS hs t.property).mp heq)
      obtain ⟨b',hb',hz',hst⟩ := hst
      change s = (t : ℝ) at hst
      subst s
      refine ⟨⟨z,hz,?_⟩,p,hpS,rfl⟩
      apply hai (hgK' none hz) (hgK' (some side) hpS)
      exact (hgv' none z hz).trans (heq.trans (hgv' (some side) p hpS).symm)
  have hLdis (side : Bool) : Disjoint (L side false) (L side true) := by
    apply disjoint_left.mpr
    rintro x ⟨p,hp,rfl⟩ ⟨q,hq,heq⟩
    have hpq := hgi' (some side) (stripEndEdge_subset true hq) (stripEndEdge_subset false hp) heq
    have hp1 : p.1 = 1 := hp.1
    have hq1 : q.1 = 0 := hq.1
    have h := congrArg Prod.fst hpq
    linarith
  have hMdis : Disjoint (M (some false)) (M (some true)) := by
    apply disjoint_left.mpr
    rintro x ⟨p,hp,rfl⟩ ⟨q,hq,heq⟩
    have hphys : diskStrip (P true) (q,t) = diskStrip (P false) (p,t) :=
      (hgv' (some true) q hq).symm.trans ((congrArg a heq).trans (hgv' (some false) p hp))
    have hmem (b : Bool) (z : P2) (hz : z ∈ stripBase) : diskStrip (P b) (z,t) ∈ (P b).closedStrip :=
      (diskStrip_properties (P b)).2.2.2.subset ⟨(z,t),⟨hz,t.property⟩,rfl⟩
    exact disjoint_left.mp hdis (hmem false p hp) (hphys ▸ hmem true q hq)
  obtain ⟨K',N,hK',hKK',hNK',hNs,hdim,hcount⟩ :=
    exists_three_disk_four_arc_neighborhood_model K hK M m hM L l hL
      (fun i => image_subset_iff.mpr (hgK' i)) hcontact hLdis hMdis
  refine ⟨K',N,hK',hKK',hNK',hNs.trans ?_,hdim,hcount⟩
  ext x
  have him : x ∈ M none ∪ (M (some false) ∪ M (some true)) ↔ ∃ i, x ∈ M i := by
    simp only [Option.exists,Bool.exists_bool,mem_union]
  rw [him]
  constructor
  · rintro ⟨i,z,hz,rfl⟩
    exact ⟨hgK' i hz,mem_iUnion.mpr ⟨i,⟨⟨z,hz⟩,(hgv' i z hz).symm⟩⟩⟩
  · rintro ⟨hx,hxa⟩
    obtain ⟨i,z,hz⟩ := mem_iUnion.mp hxa
    refine ⟨i,z,z.property,?_⟩
    exact hai (hgK' i z.property) hx ((hgv' i z z.property).trans hz)

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
