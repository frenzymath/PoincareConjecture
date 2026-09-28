import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.RectangleCornerModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.SharedCornerProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.TwoCapBeltExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleBoundaryCover

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_original_rectangle_prism_of_cap_labels
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
        (D z.1.1).carrier z.1.2 ∩ (D w.1.1).carrier w.1.2 = (D z.1.1).side z.1.2 b) :
    ∃ flip : CutBallRectangle D B → Bool,
      (∀ z, owner z.1.1 ((D z.1.1).cap z.1.2 (flip z)) = i₀ ∧
        owner z.1.1 ((D z.1.1).cap z.1.2 (!(flip z))) = i₁) ∧
      ∃ H : (cut i₀ ×ˢ I : Set (E × ℝ)) ≃ₜ B, H.IsFinitePL ∧
        (∀ (x : E) (hx : x ∈ cut i₀), (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
        (∀ x, (H x : E) ∈ cut i₀ ↔ (x : E × ℝ).2 = 0) ∧
        (∀ x, (H x : E) ∈ cut i₁ ↔ (x : E × ℝ).2 = 1) ∧
        ∀ z x, (H x : E) ∈ (D z.1.1).carrier z.1.2 ↔
          (x : E × ℝ).1 ∈ (D z.1.1).arc ((D z.1.1).cap z.1.2 (flip z)) := by
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
  have hBall (z : CutBallRectangle D B) : IsFinitePLBallPair (ℝ × ℝ) (M z)
      ((W z ∪ Z z) ∪ (L z false ∪ L z true)) := by
    cases he : flip z
    · simpa only [M,W,Z,L,OriginalFaceRectangles.side,he,Bool.not_false] using
        (D z.1.1).regionBall z.1.2
    · simpa only [M,W,Z,L,OriginalFaceRectangles.side,he,Bool.not_true,union_comm] using
        (D z.1.1).regionBall z.1.2
  obtain ⟨J,hJ,hJzero,hJM,hJbottom,hJtop⟩ := exists_belt_product_of_shared_cap_corners
    M W Z L p q (cut i₀) (cut i₁)
    (fun z b => by cases he : flip z <;> simpa only [p,q,he,Bool.not_false,Bool.not_true,
      pair_comm] using hL z b)
    (fun z b => by
      cases he : flip z
      · simpa only [p,q,he,Bool.not_false] using hcorner z b
      · simpa only [p,q,he,Bool.not_true] using (hcorner z b).symm)
    hBall (fun z => hArc z (flip z)) (fun z => hArc z (!(flip z)))
    (fun z => by
      cases he : flip z
      · simpa only [W,Z,he,Bool.not_false] using
          (D z.1.1).arcDisjoint ((D z.1.1).capDistinct z.1.2)
      · simpa only [W,Z,he,Bool.not_true] using
          ((D z.1.1).arcDisjoint ((D z.1.1).capDistinct z.1.2)).symm)
    (fun z => (D z.1.1).sides_disjoint z.1.2) hWL hZL hAL hBL hcontact
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
  refine ⟨flip,hf,H,hH,hHzero,hHbottom,hHtop,?_⟩
  intro z x
  constructor
  · intro hx
    have hxq := (hHT x).mp (mem_iUnion.mpr ⟨z,hx⟩)
    let y : ((⋃ z, W z) ×ˢ I : Set (E × ℝ)) := ⟨x,hxq,x.2.2⟩
    exact (hJM z y).mp ((hHside y) ▸ hx)
  · intro hx
    let y : ((⋃ z, W z) ×ˢ I : Set (E × ℝ)) := ⟨x,mem_iUnion.mpr ⟨z,hx⟩,x.2.2⟩
    exact (hHside y).symm ▸ (hJM z y).mpr hx

end PoincareConjecture.M76.PrismBelt
