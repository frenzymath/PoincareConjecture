import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.RectangleCornerModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalAffineBelt
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.TwoCapBeltExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleBoundaryCover

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_global_original_rectangle_prism
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [DecidableEq ι]
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite) {g : E → X} {S : Set X} {t : Finset E}
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B R : Set E} (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B R)
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (owner : ∀ f, (D f).Arc → ι)
    (hcutContact : ∀ f k i, (D f).carrier k ∩ cut i =
      (if owner f ((D f).cap k false) = i then (D f).arc ((D f).cap k false) else ∅) ∪
      (if owner f ((D f).cap k true) = i then (D f).arc ((D f).cap k true) else ∅))
    (i₀ i₁ : ι) (hne : i₀ ≠ i₁)
    (hbottom : ∀ z : CutBallRectangle D B,
      owner z.1.1 ((D z.1.1).cap z.1.2 false) = i₀ ∨
      owner z.1.1 ((D z.1.1).cap z.1.2 true) = i₀)
    (htop : ∀ z : CutBallRectangle D B,
      owner z.1.1 ((D z.1.1).cap z.1.2 false) = i₁ ∨
      owner z.1.1 ((D z.1.1).cap z.1.2 true) = i₁)
    (hcover : (cut i₀ ∪ cut i₁) ∪
      (⋃ z : CutBallRectangle D B, (D z.1.1).carrier z.1.2) = R)
    (hcontact₀ : cut i₀ ∩ (⋃ z : CutBallRectangle D B, (D z.1.1).carrier z.1.2) = rim i₀)
    (hcontact : ∀ z w : CutBallRectangle D B, z ≠ w →
      ((D z.1.1).carrier z.1.2 ∩ (D w.1.1).carrier w.1.2).Nonempty →
      ∃ b c, (D z.1.1).side z.1.2 b = (D w.1.1).side w.1.2 c ∧
        (D z.1.1).carrier z.1.2 ∩ (D w.1.1).carrier w.1.2 = (D z.1.1).side z.1.2 b)
    (G : ∀ z : CutBallRectangle D B, Square ≃ₜ (D z.1.1).carrier z.1.2)
    (hG : ∀ z, (G z).IsFinitePL)
    (hGW : ∀ z x, (G z x : E) ∈ (D z.1.1).arc ((D z.1.1).cap z.1.2 false) ↔ (x : ℝ × ℝ).2 = 0)
    (hGZ : ∀ z x, (G z x : E) ∈ (D z.1.1).arc ((D z.1.1).cap z.1.2 true) ↔ (x : ℝ × ℝ).2 = 1)
    (hGL : ∀ z b x, (G z x : E) ∈ (D z.1.1).side z.1.2 b ↔
      (x : ℝ × ℝ).1 = if b then 1 else 0)
    (hGaffine : ∀ z b t, (G z (sidePoint b t) : E) =
      AffineMap.lineMap (G z (sidePoint b 0) : E) (G z (sidePoint b 1) : E) (t : ℝ)) :
    ∃ flip : CutBallRectangle D B → Bool,
      (∀ z, owner z.1.1 ((D z.1.1).cap z.1.2 (flip z)) = i₀ ∧
        owner z.1.1 ((D z.1.1).cap z.1.2 (!(flip z))) = i₁) ∧
      ∃ H : (cut i₀ ×ˢ I : Set (E × ℝ)) ≃ₜ B, H.IsFinitePL ∧
        (∀ (x : E) (hx : x ∈ cut i₀), (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
        (∀ x, (H x : E) ∈ cut i₀ ↔ (x : E × ℝ).2 = 0) ∧
        (∀ x, (H x : E) ∈ cut i₁ ↔ (x : E × ℝ).2 = 1) ∧
        (∀ z x, (H x : E) ∈ (D z.1.1).carrier z.1.2 ↔
          (x : E × ℝ).1 ∈ (D z.1.1).arc ((D z.1.1).cap z.1.2 (flip z))) ∧
        ∀ (z : CutBallRectangle D B) (u t : I),
          (H.symm ⟨G z ⟨(u,fiberFlip (flip z) t),u.property,(fiberFlip (flip z) t).property⟩,
            z.2 (G z _).property⟩ : E × ℝ) =
            ((G z ⟨(u,fiberFlip (flip z) 0),u.property,(fiberFlip (flip z) 0).property⟩ : E),(t : ℝ)) := by
  classical
  let := K.finite_faceOfCard hK 3
  let M (z : CutBallRectangle D B) := (D z.1.1).carrier z.1.2
  let flip (z : CutBallRectangle D B) :=
    if owner z.1.1 ((D z.1.1).cap z.1.2 false) = i₀ then false else true
  have hf (z : CutBallRectangle D B) :
      owner z.1.1 ((D z.1.1).cap z.1.2 (flip z)) = i₀ ∧
      owner z.1.1 ((D z.1.1).cap z.1.2 (!(flip z))) = i₁ := by
    dsimp only [flip]
    split_ifs with h
    · refine ⟨h,?_⟩
      exact (htop z).resolve_left (fun h' => hne (h.symm.trans h'))
    · have h' := (hbottom z).resolve_left h
      exact ⟨h',(htop z).resolve_right (fun hh => hne (h'.symm.trans hh))⟩
  let W (z : CutBallRectangle D B) := (D z.1.1).arc ((D z.1.1).cap z.1.2 (flip z))
  let Z (z : CutBallRectangle D B) := (D z.1.1).arc ((D z.1.1).cap z.1.2 (!(flip z)))
  let L (z : CutBallRectangle D B) (b : Bool) := (D z.1.1).side z.1.2 b
  choose corner hcorner hL hArc hCornerContact using fun z : CutBallRectangle D B =>
    (D z.1.1).exists_corner_models z.1.2
  let p (z : CutBallRectangle D B) (b : Bool) := corner z b (flip z)
  let q (z : CutBallRectangle D B) (b : Bool) := corner z b (!(flip z))
  have hM0 (z : CutBallRectangle D B) : M z ∩ cut i₀ = W z := by
    have h := hcutContact z.1.1 z.1.2 i₀
    have hb := hf z
    cases he : flip z <;> simp only [he,Bool.not_false,Bool.not_true] at hb ⊢
    · simpa [hb.1,hb.2,Ne.symm hne,W,he,M] using h
    · simpa [hb.1,hb.2,Ne.symm hne,W,he,M] using h
  have hM1 (z : CutBallRectangle D B) : M z ∩ cut i₁ = Z z := by
    have h := hcutContact z.1.1 z.1.2 i₁
    have hb := hf z
    cases he : flip z <;> simp only [he,Bool.not_false,Bool.not_true] at hb ⊢
    · simpa [hb.1,hb.2,hne,Z,he,M] using h
    · simpa [hb.1,hb.2,hne,Z,he,M] using h
  have hWL (z : CutBallRectangle D B) (b : Bool) : W z ∩ L z b = {p z b} :=
    hCornerContact z (flip z) b
  have hZL (z : CutBallRectangle D B) (b : Bool) : Z z ∩ L z b = {q z b} :=
    hCornerContact z (!(flip z)) b
  have hAL (z : CutBallRectangle D B) (b : Bool) : cut i₀ ∩ L z b = {p z b} := by
    rw [←hWL,←hM0]
    ext x
    constructor
    · intro hx
      exact ⟨⟨(D z.1.1).side_subset_carrier z.1.2 b hx.2,hx.1⟩,hx.2⟩
    · exact fun hx => ⟨hx.1.2,hx.2⟩
  have hBL (z : CutBallRectangle D B) (b : Bool) : cut i₁ ∩ L z b = {q z b} := by
    rw [←hZL,←hM1]
    ext x
    constructor
    · intro hx
      exact ⟨⟨(D z.1.1).side_subset_carrier z.1.2 b hx.2,hx.1⟩,hx.2⟩
    · exact fun hx => ⟨hx.1.2,hx.2⟩
  have hGcorner (z : CutBallRectangle D B) (b a : Bool) :
      (G z (sidePoint b (if a then 1 else 0)) : E) = corner z b a := by
    apply (hCornerContact z a b).subset
    constructor
    · cases a
      · exact (hGW z _).mpr rfl
      · exact (hGZ z _).mpr rfl
    · exact (hGL z b _).mpr rfl
  have hrawSide (z : CutBallRectangle D B) (b : Bool) (t : I) :
      (G z (sidePoint b t) : E) = AffineMap.lineMap (corner z b false) (corner z b true) (t : ℝ) := by
    rw [hGaffine,show (G z (sidePoint b 0) : E) = corner z b false from hGcorner z b false,
      show (G z (sidePoint b 1) : E) = corner z b true from hGcorner z b true]
  let C (z : CutBallRectangle D B) := (rectangleFiberFlip (flip z)).trans (G z)
  have hC (z : CutBallRectangle D B) : (C z).IsFinitePL :=
    (rectangleFiberFlip_finitePL _).trans (hG z)
  have hCW (z : CutBallRectangle D B) (x : Square) :
      (C z x : E) ∈ W z ↔ (x : ℝ × ℝ).2 = 0 := by
    cases he : flip z
    · simpa only [C,W,he,Homeomorph.trans_apply,rectangleFiberFlip_false] using hGW z x
    · have h := hGZ z (rectangleFiberFlip true x)
      change (C z x : E) ∈ W z ↔ _
      change (G z (rectangleFiberFlip (flip z) x) : E) ∈
        (D z.1.1).arc ((D z.1.1).cap z.1.2 (flip z)) ↔ _
      rw [he]
      exact h.trans (by
        change 1-(x : ℝ × ℝ).2 = 1 ↔ (x : ℝ × ℝ).2 = 0
        constructor <;> intro hh <;> linarith)
  have hCZ (z : CutBallRectangle D B) (x : Square) :
      (C z x : E) ∈ Z z ↔ (x : ℝ × ℝ).2 = 1 := by
    cases he : flip z
    · simpa only [C,Z,he,Bool.not_false,Homeomorph.trans_apply,rectangleFiberFlip_false] using hGZ z x
    · have h := hGW z (rectangleFiberFlip true x)
      change (G z (rectangleFiberFlip (flip z) x) : E) ∈
        (D z.1.1).arc ((D z.1.1).cap z.1.2 (!(flip z))) ↔ _
      rw [he]
      exact h.trans (by
        change 1-(x : ℝ × ℝ).2 = 0 ↔ (x : ℝ × ℝ).2 = 1
        constructor <;> intro hh <;> linarith)
  have hCside (z : CutBallRectangle D B) (b : Bool) (t : I) :
      (C z (sidePoint b t) : E) = AffineMap.lineMap (p z b) (q z b) (t : ℝ) := by
    change (G z (sidePoint b (fiberFlip (flip z) t)) : E) = _
    rw [hrawSide]
    cases he : flip z
    · simp only [p,q,he,Bool.not_false,fiberFlip_false]
    · change AffineMap.lineMap (corner z b false) (corner z b true) (1-(t : ℝ)) =
        AffineMap.lineMap (p z b) (q z b) (t : ℝ)
      simpa only [p,q,he,Bool.not_true] using
        AffineMap.lineMap_apply_one_sub (corner z b false) (corner z b true) (t : ℝ)
  have hsegment (z : CutBallRectangle D B) (b : Bool) :
      L z b = segment ℝ (p z b) (q z b) := by
    cases he : flip z <;> simpa only [p,q,he,Bool.not_false,Bool.not_true,segment_symm] using
      (D z.1.1).side_eq_segment_of_corners z.1.2 b (hL z b)
  have hpq (z : CutBallRectangle D B) (b : Bool) : p z b ≠ q z b := by
    cases he : flip z
    · simpa only [p,q,he,Bool.not_false] using hcorner z b
    · simpa only [p,q,he,Bool.not_true] using (hcorner z b).symm
  obtain ⟨J,hJ,hJzero,hJM,hJbottom,hJtop,hformula⟩ := exists_global_affine_side_belt
    M W Z L p q (cut i₀) (cut i₁) hsegment hpq hAL hBL
    (fun z => (hM0 z).symm.subset.trans inter_subset_left)
    (fun z => (hM1 z).symm.subset.trans inter_subset_left)
    C hC hCW hCZ hCside hcontact
  have hWwhole : cut i₀ ∩ (⋃ z, M z) = ⋃ z, W z := by
    rw [inter_iUnion]
    congr 1
    funext z
    exact (inter_comm _ _).trans (hM0 z)
  have hZwhole : cut i₁ ∩ (⋃ z, M z) = ⋃ z, Z z := by
    rw [inter_iUnion]
    congr 1
    funext z
    exact (inter_comm _ _).trans (hM1 z)
  have hBase : IsFinitePLBallPair (ℝ × ℝ) (cut i₀) (⋃ z, W z) :=
    (hcontact₀.symm.trans hWwhole) ▸ hcut i₀
  obtain ⟨H,hH,hHzero,hHside,hHbottom,hHtop,hHT⟩ := exists_two_cap_prism_extension
    hB hBase hcover (hdis hne) hWwhole hZwhole J hJ hJzero hJbottom hJtop
  refine ⟨flip,hf,H,hH,hHzero,hHbottom,hHtop,?_,?_⟩
  · intro z x
    constructor
    · intro hx
      have hxq := (hHT x).mp (mem_iUnion.mpr ⟨z,hx⟩)
      let y : ((⋃ z, W z) ×ˢ I : Set (E × ℝ)) := ⟨x,hxq,x.2.2⟩
      exact (hJM z y).mp ((hHside y) ▸ hx)
    · intro hx
      let y : ((⋃ z, W z) ×ˢ I : Set (E × ℝ)) := ⟨x,mem_iUnion.mpr ⟨z,hx⟩,x.2.2⟩
      exact (hHside y).symm ▸ (hJM z y).mpr hx
  · intro z u t
    let y : ((⋃ z, W z) ×ˢ I : Set (E × ℝ)) :=
      ⟨((C z ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E),t),
        mem_iUnion.mpr ⟨z,(hCW z _).mpr rfl⟩,t.property⟩
    have he : H ⟨y,hBase.1 y.property.1,y.property.2⟩ =
        ⟨C z ⟨(u,t),u.property,t.property⟩,z.2 (C z _).property⟩ :=
      Subtype.ext ((hHside y).trans (hformula z u t))
    have hh := congrArg (fun x : B => (H.symm x : E × ℝ)) he
    have hzero : rectangleFiberFlip (flip z) ⟨(u,0),u.property,le_rfl,zero_le_one⟩ =
        ⟨(u,fiberFlip (flip z) 0),u.property,(fiberFlip (flip z) 0).property⟩ := rfl
    simpa only [H.symm_apply_apply,y,C,Homeomorph.trans_apply,rectangleFiberFlip_apply,hzero] using hh.symm

end PoincareConjecture.M76.PrismBelt
