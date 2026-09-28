import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.RectangleCornerContacts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem finitePL_square_coordinate_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M C : Set E} (G : Square ≃ₜ M) (hG : G.IsFinitePL) (hCM : C ⊆ M)
    (vertical : Bool) (u : I)
    (hC : ∀ x, (G x : E) ∈ C ↔
      (if vertical then (x : ℝ × ℝ).1 else (x : ℝ × ℝ).2) = u) :
    IsFinitePLBallPair ℝ C
      {(G ⟨(if vertical then ((u : ℝ),0) else (0,(u : ℝ))),by
        cases vertical <;> exact ⟨by first | exact u.2 | norm_num,
          by first | exact u.2 | norm_num⟩⟩ : E),
       (G ⟨(if vertical then ((u : ℝ),1) else (1,(u : ℝ))),by
        cases vertical <;> exact ⟨by first | exact u.2 | norm_num,
          by first | exact u.2 | norm_num⟩⟩ : E)} := by
  let F : ℝ →ᴬ[ℝ] (ℝ × ℝ) := if vertical then
    (ContinuousAffineMap.const ℝ ℝ (u : ℝ)).prod (ContinuousAffineMap.id ℝ ℝ)
    else (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ (u : ℝ))
  have hFi : Function.Injective F := by
    cases vertical
    · exact fun x y h => congrArg Prod.fst h
    · exact fun x y h => congrArg Prod.snd h
  have hFS : F '' I ⊆ Square := by
    rintro _ ⟨x,hx,rfl⟩
    cases vertical
    · exact ⟨hx,u.2⟩
    · exact ⟨u.2,hx⟩
  obtain ⟨f,hf,hfG⟩ := hG
  have hfi : InjOn f Square := by
    intro x hx y hy he
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hfG ⟨x,hx⟩).trans (he.trans (hfG ⟨y,hy⟩).symm))))
  have hball := (isFinitePLBallPair_affine_interval zero_lt_one F hFi.injOn).image_of_subset hf hFS hfi
  have himage : f '' (F '' I) = C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have he : (G ⟨x,hFS hx⟩ : E) ∈ C := by
        apply (hC _).mpr
        obtain ⟨z,hz,rfl⟩ := hx
        cases vertical <;> rfl
      exact (hfG ⟨x,hFS hx⟩) ▸ he
    · intro hy
      have hyM : y ∈ M := hCM hy
      let x := G.symm ⟨y,hyM⟩
      have hxC : (G x : E) ∈ C := by simpa [x] using hy
      have hx := (hC x).mp hxC
      have hxF : (x : ℝ × ℝ) ∈ F '' I := by
        cases vertical
        · exact ⟨(x : ℝ × ℝ).1,x.2.1,Prod.ext rfl hx.symm⟩
        · exact ⟨(x : ℝ × ℝ).2,x.2.2,Prod.ext hx.symm rfl⟩
      exact ⟨x,hxF,(hfG x).symm.trans (congrArg Subtype.val (G.apply_symm_apply _))⟩
  rw [himage,image_pair] at hball
  convert hball using 1 <;> congr 1
  · cases vertical <;> exact hfG ⟨F 0,hFS (mem_image_of_mem F ⟨le_rfl,zero_le_one⟩)⟩
  · congr 1
    cases vertical <;> exact hfG ⟨F 1,hFS (mem_image_of_mem F ⟨zero_le_one,le_rfl⟩)⟩

theorem OriginalFaceRectangles.exists_corner_models
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (k : D.Region) :
    ∃ p : Bool → Bool → E,
      (∀ b, p b false ≠ p b true) ∧
      (∀ b, IsFinitePLBallPair ℝ (D.side k b) {p b false,p b true}) ∧
      (∀ a, IsFinitePLBallPair ℝ (D.arc (D.cap k a)) {p false a,p true a}) ∧
      ∀ a b, D.arc (D.cap k a) ∩ D.side k b = {p b a} := by
  obtain ⟨G,hG,hW,hZ,hL,hR⟩ := D.rectangle k
  let v (b : Bool) : I := ⟨if b then 1 else 0,by cases b <;> norm_num⟩
  let p (b a : Bool) : E := G ⟨((v b : ℝ),(v a : ℝ)),(v b).2,(v a).2⟩
  have hcap (a : Bool) (x : Square) : (G x : E) ∈ D.arc (D.cap k a) ↔
      (x : ℝ × ℝ).2 = v a := by cases a <;> first | exact hW x | exact hZ x
  have hside (b : Bool) (x : Square) : (G x : E) ∈ D.side k b ↔
      (x : ℝ × ℝ).1 = v b := by cases b <;> first | exact hL x | exact hR x
  have hcapM (a : Bool) : D.arc (D.cap k a) ⊆ D.carrier k := by
    intro x hx
    apply (D.regionBall k).1
    cases a
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
  refine ⟨p,?_,?_,?_,?_⟩
  · intro b he
    have hp := G.injective (Subtype.ext he)
    have hx := congrArg (fun x : Square => (x : ℝ × ℝ).2) hp
    change (0 : ℝ) = 1 at hx
    exact zero_ne_one hx
  · intro b
    exact finitePL_square_coordinate_interval G hG (D.side_subset_carrier k b) true (v b) (hside b)
  · intro a
    exact finitePL_square_coordinate_interval G hG (hcapM a) false (v a) (hcap a)
  · intro a b
    ext x
    constructor
    · rintro ⟨hxc,hxs⟩
      let y := G.symm ⟨x,hcapM a hxc⟩
      have hGy : (G y : E) = x := congrArg Subtype.val (G.apply_symm_apply _)
      have hyc := (hcap a y).mp (hGy.symm ▸ hxc)
      have hys := (hside b y).mp (hGy.symm ▸ hxs)
      have he : y = ⟨((v b : ℝ),(v a : ℝ)),(v b).2,(v a).2⟩ :=
        Subtype.ext (Prod.ext hys hyc)
      exact hGy.symm.trans (congrArg (fun z : Square => (G z : E)) he)
    · rintro rfl
      exact ⟨(hcap a _).mpr rfl,(hside b _).mpr rfl⟩

end PoincareConjecture.M76.PrismBelt
