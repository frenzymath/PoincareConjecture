import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalFiberFlip
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.PrescribedRectangleSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MatchedRectangleHeight

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_affine_segment_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Set E} {p q : E} (hpq : p ≠ q) (hL : L = segment ℝ p q) :
    ∃ d : I ≃ₜ L, d.IsFinitePL ∧ ∀ t : I, (d t : E) = AffineMap.lineMap p q (t : ℝ) := by
  obtain ⟨K,_,hK,hKs,_,_⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).exists_finite_carrier_and_rim_complexes
  let f : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap p q
  have hf : FinitePiecewiseAffineOn f I := ⟨K,hK,hKs,K.affineOnFaces_affine f⟩
  have himage : f '' I = L := by
    rw [hL,segment_eq_image_lineMap]
    rfl
  have hex := hf.exists_homeomorph_image (AffineMap.lineMap_injective ℝ hpq).injOn
  rw [himage] at hex
  exact hex

theorem OriginalFaceRectangles.side_eq_segment_of_corners
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool)
    {p q : E} (hL : IsFinitePLBallPair ℝ (D.side k b) {p,q}) :
    D.side k b = segment ℝ p q := by
  obtain ⟨hei,_,_,_,_,_,hlohi,_⟩ := D.edgeData k b
  have hstd := isFinitePLBallPair_affine_interval hlohi (D.edge k b) hei.injOn
  have hpair := hL.boundary_eq_of_same_carrier hstd
  have hside : D.side k b = segment ℝ (D.edge k b (D.lo k b)) (D.edge k b (D.hi k b)) := by
    change D.edge k b '' Icc (D.lo k b) (D.hi k b) = _
    rw [←segment_eq_Icc hlohi.le]
    exact image_segment ℝ (D.edge k b).toAffineMap _ _
  rcases pair_eq_pair_iff.mp hpair with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · simpa only [hp,hq] using hside
  · simpa only [hp,hq,segment_symm] using hside

theorem OriginalFaceRectangles.exists_affine_side_fiber_chart
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (k : D.Region) :
    ∃ p : Bool → Bool → E,
      (∀ b, p b false ≠ p b true) ∧
      (∀ b, IsFinitePLBallPair ℝ (D.side k b) {p b false,p b true}) ∧
      (∀ a, IsFinitePLBallPair ℝ (D.arc (D.cap k a)) {p false a,p true a}) ∧
      (∀ a b, D.arc (D.cap k a) ∩ D.side k b = {p b a}) ∧
      ∃ G : Square ≃ₜ D.carrier k, G.IsFinitePL ∧
        (∀ z, (G z : E) ∈ D.arc (D.cap k false) ↔ (z : ℝ × ℝ).2 = 0) ∧
        (∀ z, (G z : E) ∈ D.arc (D.cap k true) ↔ (z : ℝ × ℝ).2 = 1) ∧
        (∀ b z, (G z : E) ∈ D.side k b ↔ (z : ℝ × ℝ).1 = if b then 1 else 0) ∧
        ∀ b t, (G (sidePoint b t) : E) = AffineMap.lineMap (p b false) (p b true) (t : ℝ) := by
  obtain ⟨p,hp,hL,hArc,hcontact⟩ := D.exists_corner_models k
  choose d hd hdval using fun b => exists_affine_segment_chart (hp b)
    (D.side_eq_segment_of_corners k b (hL b))
  have h0 (b : Bool) : (d b 0 : E) = p b false := by
    simpa using hdval b 0
  have h1 (b : Bool) : (d b 1 : E) = p b true := by
    simpa using hdval b 1
  have hneq (a : Bool) : p false a ≠ p true a := by
    intro he
    have hlf : p false a ∈ D.side k false :=
      ((hcontact a false).symm.subset rfl).2
    have hrt : p true a ∈ D.side k true := ((hcontact a true).symm.subset rfl).2
    exact disjoint_left.mp (D.sides_disjoint k) hlf (he.symm ▸ hrt)
  obtain ⟨G,hG,hGl,hGr,hGW,hGZ,hGL,hGR⟩ := exists_rectangle_with_prescribed_vertical_sides
    (D.regionBall k) (hArc false) (hArc true) (hneq false) (hneq true)
    (d false) (d true) (hd false) (hd true) (h0 false) (h1 false) (h0 true) (h1 true)
    (D.arcDisjoint (D.capDistinct k)) (D.sides_disjoint k)
    (hcontact false false) (hcontact false true) (hcontact true false) (hcontact true true)
  refine ⟨p,hp,hL,hArc,hcontact,G,hG,hGW,hGZ,?_,?_⟩
  · intro b z
    cases b
    · exact hGL z
    · exact hGR z
  · intro b t
    cases b
    · exact (hGl t).trans (hdval false t)
    · exact (hGr t).trans (hdval true t)

end PoincareConjecture.M76.PrismBelt
