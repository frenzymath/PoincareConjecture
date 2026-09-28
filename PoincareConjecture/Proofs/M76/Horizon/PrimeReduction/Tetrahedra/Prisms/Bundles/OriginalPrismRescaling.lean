import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalPrismRescalingContact

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 600000 in
theorem exists_original_prism_rescaling
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (F : OriginalTetrahedralCutFamily K g S)
    (i₀ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (hH : ∀ j, (H j).IsFinitePL)
    (flip : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (F.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (F.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hC : ∀ j, (C j).IsFinitePL)
    (hCv : ∀ j x, (C j x : E) = H j (trimProduct (F.cut j.1.1 (i₀ j)) x))
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S))
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2) :
    ∃ r : E → E, FinitePiecewiseAffineOn r (⋃ j, prismTrim (H j)) ∧
      ContinuousOn r (⋃ j, prismTrim (H j)) ∧
      MapsTo r (⋃ j, prismTrim (H j)) K.space ∧
      (∀ j x, r (C j x) = H j (prismScaleProduct (F.cut j.1.1 (i₀ j)) δ hδ hhalf x)) ∧
      r '' (⋃ j, prismTrim (H j)) = ⋃ j, prismTrimAt (H j) δ := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite Cell := by dsimp [Cell,RegularOriginalCutCell]; infer_instance
  choose Cδ hCδ hCδv using fun j : Cell => exists_finitePL_prism_scale_chart (H j) (hH j) δ hδ hhalf
  let e (j : Cell) := (C j).symm.trans (Cδ j)
  have he (j : Cell) : (e j).IsFinitePL := (hC j).symm.trans (hCδ j)
  have hev (j : Cell) (x : prismTrim (H j)) : (e j x : E) =
      H j (prismScaleProduct (F.cut j.1.1 (i₀ j)) δ hδ hhalf ((C j).symm x)) := hCδv j _
  have hagree (j l : Cell) (x : E) (hj : x ∈ prismTrim (H j)) (hl : x ∈ prismTrim (H l)) :
      (e j ⟨x,hj⟩ : E) = e l ⟨x,hl⟩ := by
    rw [hev,hev]
    exact original_prism_rescaling_agrees K g hgi D G hW hZ hL haffine F i₀ H flip hformula
      C hCv havoid δ hδ hhalf j l x hj hl
  let r : E → E := fun x => if hx : x ∈ ⋃ j, prismTrim (H j) then
    e (mem_iUnion.mp hx).choose ⟨x,(mem_iUnion.mp hx).choose_spec⟩ else 0
  have hrval (j : Cell) (x : prismTrim (H j)) : r x = (e j x : E) := by
    have hx : (x : E) ∈ ⋃ j, prismTrim (H j) := mem_iUnion.mpr ⟨j,x.property⟩
    dsimp only [r]
    rw [dif_pos hx]
    exact hagree _ j x _ x.property
  have hrPL (j : Cell) : FinitePiecewiseAffineOn r (prismTrim (H j)) := by
    obtain ⟨f,hf,hfv⟩ := he j
    exact hf.congr fun x hx => (hfv ⟨x,hx⟩).symm.trans (hrval j ⟨x,hx⟩).symm
  have hrPLU := FinitePiecewiseAffineOn.iUnion hrPL
  refine ⟨r,hrPLU,hrPLU.continuousOn,?_,?_,?_⟩
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    rw [hrval j ⟨x,hj⟩]
    exact K.convexHull_subset_space j.1.1.2.1 (F.ball_subset_tetrahedron j.1.1 j.1.2
      (prismTrimAt_subset (H j) δ (e j ⟨x,hj⟩).property))
  · intro j x
    rw [hrval j (C j x),hev,(C j).symm_apply_apply]
  · ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      rw [hrval j ⟨x,hj⟩]
      exact mem_iUnion.mpr ⟨j,(e j ⟨x,hj⟩).property⟩
    · intro hy
      obtain ⟨j,hj⟩ := mem_iUnion.mp hy
      let x := (e j).symm ⟨y,hj⟩
      refine ⟨x,mem_iUnion.mpr ⟨j,x.property⟩,?_⟩
      rw [hrval j x]
      exact congrArg Subtype.val ((e j).apply_symm_apply ⟨y,hj⟩)

end PoincareConjecture.M76.PrismBelt
