import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFiniteModelBallImages
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskModelAnnulusCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.AnnulusDoubleSphereProduct
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_original_annulus_double_product
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R N V : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hN : IsCompact N) (he : PLDomain e N)
    (hPN : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) N) (hVN : V ⊆ N)
    {Z : Set E} (f : E → X) (hf : PolyhedralPLInCharts e f Z) (hfi : InjOn f Z)
    (C q : Bool → Set E)
    (hC : ∀ s, IsFinitePLBallPair P2 (C s) (q s)) (hCZ : ∀ s, C s ⊆ Z)
    (b : ChartwisePLBall e V
      ((P.map '' (Rim ×ˢ J)) ∪ ((f '' C false) ∪ (f '' C true))))
    (hrim : ∀ s, f '' q s =
      P.map '' (Rim ×ˢ {if s then (1/2 : ℝ) else -(1/2)}))
    (hmeet : ∀ s, (f '' C s) ∩ (P.map '' (Rim ×ˢ J)) =
      P.map '' (Rim ×ˢ {if s then (1/2 : ℝ) else -(1/2)}))
    (hdis : Disjoint (f '' C true) (f '' C false))
    (hcontact : V ∩ P.closedStrip = P.map '' (Rim ×ˢ J)) :
    ∃ (H : (V ∪ P.closedStrip : Set X) ≃ₜ
        (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
      (σ : P3 × ℝ → X),
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X)) ∧
      ∀ s (x : (V ∪ P.closedStrip : Set X)),
        (x : X) ∈ (f '' C s) ∪
          (P.map '' (Disk ×ˢ {if s then (1/2 : ℝ) else -(1/2)})) ↔
          (H x : P3 × ℝ).2 = if s then (1 : ℝ) else 0 := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨T,F,K,L,G,hFc,hF,hK,_,_,hKs,_,hGF,_,hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      e he.compatible he.cover hN he.halfspace
  have hFi : InjOn F N := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hGF ⟨x,hx⟩).trans (hxy.trans (hGF ⟨y,hy⟩).symm))))
  let band := P.map '' (Rim ×ˢ J)
  let cap : Bool → Set X := fun s => P.map '' (Disk ×ˢ {if s then (1/2 : ℝ) else -(1/2)})
  let rim : Bool → Set X := fun s => P.map '' (Rim ×ˢ {if s then (1/2 : ℝ) else -(1/2)})
  have hcapV (s : Bool) : f '' C s ⊆ V := by
    apply subset_trans _ b.boundary_subset
    cases s
    · exact subset_union_left.trans subset_union_right
    · exact subset_union_right.trans subset_union_right
  have hstripN : P.closedStrip ⊆ N := by
    rintro _ ⟨z,hz,rfl⟩
    exact hPN ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hbandstrip : band ⊆ P.closedStrip :=
    image_mono (prod_mono sphere_subset_closedBall subset_rfl)
  have hcapstrip (s : Bool) : cap s ⊆ P.closedStrip := by
    apply image_mono
    intro z hz
    refine ⟨hz.1,?_⟩
    have ht : z.2 = if s then (1/2 : ℝ) else -(1/2) := hz.2
    rw [ht]
    cases s <;> norm_num
  have hphysicalmeet (s : Bool) : cap s ∩ band = rim s := by
    ext x
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,⟨w,hw,hwz⟩⟩
      have hzJ := hcapstrip s ⟨z,hz,rfl⟩
      have hzfull : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := by
        refine ⟨hz.1,?_⟩
        have ht : z.2 = if s then (1/2 : ℝ) else -(1/2) := hz.2
        rw [ht]
        cases s <;> norm_num
      have hwfull : w ∈ Disk ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨sphere_subset_closedBall hw.1,by linarith [hw.2.1],by linarith [hw.2.2]⟩
      have hwz' := P.injective hwfull hzfull hwz
      exact ⟨z,⟨(congrArg Prod.fst hwz') ▸ hw.1,hz.2⟩,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,⟨sphere_subset_closedBall hz.1,hz.2⟩,rfl⟩,⟨z,⟨hz.1,?_⟩,rfl⟩⟩
      have ht : z.2 = if s then (1/2 : ℝ) else -(1/2) := hz.2
      rw [ht]
      cases s <;> norm_num
  have hphysicaldis : Disjoint (cap true) (cap false) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,hzx⟩ ⟨w,hw,hwx⟩
    have hzt : z.2 = (1/2 : ℝ) := hz.2
    have hwt : w.2 = -(1/2 : ℝ) := hw.2
    have hzi : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := ⟨hz.1,by rw [hzt]; norm_num⟩
    have hwi : w ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := ⟨hw.1,by rw [hwt]; norm_num⟩
    have hh := congrArg Prod.snd (P.injective hzi hwi (hzx.trans hwx.symm))
    rw [hzt,hwt] at hh
    norm_num at hh
  have himageinter {A B : Set X} (hAN : A ⊆ N) (hBN : B ⊆ N) :
      F '' A ∩ F '' B = F '' (A ∩ B) :=
    (image_inter_on (fun _ hx _ hy hxy => hFi (hBN hx) (hAN hy) hxy)).symm
  have himagedis {A B : Set X} (hAN : A ⊆ N) (hBN : B ⊆ N)
      (hAB : Disjoint A B) : Disjoint (F '' A) (F '' B) := by
    rw [disjoint_iff_inter_eq_empty,himageinter hAN hBN,hAB.inter_eq,image_empty]
  let balls : Bool → Set (T → ℝ × V3) := fun a => if a then F '' P.closedStrip else F '' V
  let caps : Bool → Bool → Set (T → ℝ × V3) := fun a s =>
    if a then F '' cap s else F '' (f '' C s)
  let rims : Bool → Set (T → ℝ × V3) := fun s => F '' rim s
  have hballs (a : Bool) : IsFinitePLBallPair V3 (balls a)
      ((F '' band) ∪ (caps a false ∪ caps a true)) := by
    cases a
    · simpa only [balls,caps,Bool.false_eq_true,↓reduceIte,image_union,band] using
        b.finitePLBallPair_image hVN F hF hFi
    · obtain ⟨bp⟩ := P.exists_closedStrip_ball
      have hb := bp.finitePLBallPair_image hstripN F hF hFi
      have hend : P.endDisks = cap false ∪ cap true := by
        change P.map '' (Disk ×ˢ {-(1/2 : ℝ),1/2}) = _
        have hends : ({-(1/2 : ℝ),1/2} : Set ℝ) = {-(1/2 : ℝ)} ∪ {1/2} := by
          ext x
          simp [or_comm]
        rw [hends,prod_union,image_union]
        rfl
      simpa only [balls,caps,↓reduceIte,hend,image_union,band] using hb
  have hcaps (a s : Bool) : IsFinitePLBallPair P2 (caps a s) (rims s) := by
    cases a
    · have h := finitePLBallPair_original_image (hC s) hf (hCZ s) hfi
        (fun x hx => hVN (hcapV s ⟨x,hx,rfl⟩)) hF hFi
      simpa only [caps,rims,Bool.false_eq_true,↓reduceIte,hrim,rim] using h
    · let t : ℝ := if s then 1/2 else -(1/2)
      have hd : IsFinitePLBallPair P2 Disk Rim :=
        (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
          (ContinuousLinearEquiv.ofFinrankEq (by simp) : V2 ≃L[ℝ] P2)
      have hsub : Disk ×ˢ {t} ⊆ Disk ×ˢ Icc (-1 : ℝ) 1 := by
        intro z hz
        refine ⟨hz.1,?_⟩
        rw [show z.2=t from hz.2]
        cases s <;> norm_num [t]
      have h := finitePLBallPair_original_image (hd.prod_singleton t) P.polyhedral hsub
        P.injective (fun z hz => hPN (hsub hz)) hF hFi
      exact h
  have hmeets (a s : Bool) : caps a s ∩ (F '' band) = rims s := by
    cases a
    · change F '' (f '' C s) ∩ F '' band = F '' rim s
      rw [himageinter ((hcapV s).trans hVN) (hbandstrip.trans hstripN),hmeet s]
    · change F '' cap s ∩ F '' band = F '' rim s
      rw [himageinter ((hcapstrip s).trans hstripN) (hbandstrip.trans hstripN),hphysicalmeet s]
  have hcapdis (a : Bool) : Disjoint (caps a true) (caps a false) := by
    cases a
    · exact himagedis ((hcapV true).trans hVN) ((hcapV false).trans hVN) hdis
    · exact himagedis ((hcapstrip true).trans hstripN) ((hcapstrip false).trans hstripN) hphysicaldis
  have hballcontact : balls false ∩ balls true = F '' band := by
    change F '' V ∩ F '' P.closedStrip = F '' band
    rw [himageinter hVN hstripN,hcontact]
  obtain ⟨a,ha,hamark⟩ := P.exists_finite_model_annulus_coordinates F hF hFi hPN
  obtain ⟨M,hM,hMmark⟩ := exists_finitePL_sphere_product_of_annulus_double
    balls caps rims hballs hcaps hmeets hcapdis hballcontact a ha hamark
  have hU : V ∪ P.closedStrip ⊆ N := union_subset hVN hstripN
  let : CompactSpace (V ∪ P.closedStrip : Set X) :=
    isCompact_iff_compactSpace.mp
      (b.isCompact.union (Classical.choice P.exists_closedStrip_ball).isCompact)
  let U : (V ∪ P.closedStrip : Set X) ≃ₜ (balls false ∪ balls true : Set (T → ℝ × V3)) :=
    (Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn F (V ∪ P.closedStrip) (hFi.mono hU))
      ((hFc.comp continuous_subtype_val).subtype_mk _)).trans
        (Homeomorph.setCongr (image_union F V P.closedStrip))
  let H := U.trans M
  obtain ⟨g,_,hg,hgPL⟩ := exists_polyhedral_PL_model_inverse e K hK G F subset_rfl
    ⟨P.map (0,0),hPN ⟨by simp,by norm_num⟩⟩ hGF hproj
  obtain ⟨m,hm,hmval⟩ := hM.symm
  have hmK : MapsTo m (frontier (halfBall 1) ×ˢ I) K.space := by
    intro x hx
    rw [←hmval ⟨x,hx⟩,hKs]
    rcases (M.symm ⟨x,hx⟩).property with h | h
    · exact image_mono hVN h
    · exact image_mono hstripN h
  let σ : P3 × ℝ → X := fun x => g (m x)
  have hσ : PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) := by
    obtain ⟨JJ,hJ,hJs,hfaces⟩ := hm
    rw [←hJs]
    exact hgPL.comp_finitePiecewiseAffineOn JJ hJ ⟨JJ,hJ,rfl,hfaces⟩
      (fun z hz => hmK (hJs.subset hz))
  have hUval (x : (V ∪ P.closedStrip : Set X)) : (U x : T → ℝ × V3) = F x := rfl
  have hσval (z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ))) : σ z = (H.symm z : X) := by
    have hmz : m z = (M.symm z : T → ℝ × V3) := (hmval z).symm
    change (g (m z) : X) = _
    rw [hg ⟨m z,hmK z.property⟩]
    apply hFi (G.symm ⟨m z,hmK z.property⟩).property (hU (H.symm z).property)
    rw [←hGF,G.apply_symm_apply]
    change m z = F (H.symm z)
    rw [hmz]
    exact (congrArg Subtype.val (U.apply_symm_apply _)).symm.trans
      (hUval (U.symm (M.symm z)))
  refine ⟨H,σ,hσ,hσval,?_⟩
  intro s x
  have hmem : (x : X) ∈ (f '' C s) ∪ cap s ↔
      (U x : T → ℝ × V3) ∈ caps false s ∪ caps true s := by
    change _ ↔ F x ∈ F '' (f '' C s) ∪ F '' cap s
    rw [←image_union]
    constructor
    · exact fun hx => ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      have hyN : y ∈ N := by
        rcases hy with hy | hy
        · exact hVN (hcapV s hy)
        · exact hstripN (hcapstrip s hy)
      exact hFi hyN (hU x.property) hyx ▸ hy
  exact hmem.trans (hMmark s (U x))

end PoincareConjecture.M76.OriginalDiskProduct
