import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalPrismRescalingContact
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismRescalingInverse
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularPrismAffineFiber



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 700000 in
theorem exists_original_prism_trim_homeomorph
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
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2)
    (Cδ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt (H j) δ)
    (hCδ : ∀ j, (Cδ j).IsFinitePL)
    (hCδv : ∀ j x, (Cδ j x : E) = H j (prismScaleProduct (F.cut j.1.1 (i₀ j)) δ hδ hhalf x))
    (havoidδ : Disjoint (⋃ j, prismTrimAt (H j) δ) (g ⁻¹' S)) :
    ∃ T : (⋃ j, prismTrim (H j)) ≃ₜ (⋃ j, prismTrimAt (H j) δ),
      T.IsFinitePL ∧ T.symm.IsFinitePL ∧
      (∀ j x, (T ⟨C j x,mem_iUnion.mpr ⟨j,(C j x).property⟩⟩ : E) = Cδ j x) ∧
      ∀ x, connectedComponentIn (K.space \ g ⁻¹' S) (T x : E) =
        connectedComponentIn (K.space \ g ⁻¹' S) (x : E) := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite Cell := by dsimp [Cell,RegularOriginalCutCell]; infer_instance
  let e (j : Cell) := (C j).symm.trans (Cδ j)
  have he (j : Cell) : (e j).IsFinitePL := (hC j).symm.trans (hCδ j)
  have hev (j : Cell) (x : prismTrim (H j)) : (e j x : E) =
      H j (prismScaleProduct (F.cut j.1.1 (i₀ j)) δ hδ hhalf ((C j).symm x)) := hCδv j _
  have hagree (j l : Cell) (x : E) (hj : x ∈ prismTrim (H j)) (hl : x ∈ prismTrim (H l)) :
      (e j ⟨x,hj⟩ : E) = e l ⟨x,hl⟩ := by
    rw [hev,hev]
    exact original_prism_rescaling_agrees K g hgi D G hW hZ hL haffine F i₀ H flip hformula
      C hCv havoid δ hδ hhalf j l x hj hl
  have hinvagree (j l : Cell) (x : E)
      (hj : x ∈ prismTrimAt (H j) δ) (hl : x ∈ prismTrimAt (H l) δ) :
      ((e j).symm ⟨x,hj⟩ : E) = (e l).symm ⟨x,hl⟩ := by
    have hxS : g x ∉ S := fun hs => disjoint_left.mp havoidδ (mem_iUnion.mpr ⟨j,hj⟩) hs
    have hh := original_regular_prism_affine_fiber_agrees K g hgi D G hW hZ hL haffine
      F i₀ H flip hformula j l x (prismTrimAt_subset (H j) δ hj) (prismTrimAt_subset (H l) δ hl)
      hxS ((1/4-δ)/(1-2*δ))
      (quarter_prism_inverse_admissible (H j) δ hδ hhalf (Cδ j) (hCδv j) ⟨x,hj⟩)
      (quarter_prism_inverse_admissible (H l) δ hδ hhalf (Cδ l) (hCδv l) ⟨x,hl⟩)
    exact (quarter_prism_inverse_eq_affine (H j) (C j) (hCv j) δ hδ hhalf
      (Cδ j) (hCδv j) ⟨x,hj⟩).trans
      (hh.trans (quarter_prism_inverse_eq_affine (H l) (C l) (hCv l) δ hδ hhalf
        (Cδ l) (hCδv l) ⟨x,hl⟩).symm)
  have hover (j l : Cell) (x : prismTrim (H j)) :
      (x : E) ∈ prismTrim (H l) ↔ (e j x : E) ∈ prismTrimAt (H l) δ := by
    constructor
    · intro hx
      exact (hagree j l x x.property hx).symm ▸ (e l ⟨x,hx⟩).property
    · intro hx
      have hh := hinvagree j l (e j x) (e j x).property hx
      rw [(e j).symm_apply_apply] at hh
      exact hh.symm ▸ ((e l).symm ⟨e j x,hx⟩).property
  obtain ⟨T,hT,hvalue⟩ := Homeomorph.exists_iUnion_finitePL
    (fun j => prismTrim (H j)) (fun j => prismTrimAt (H j) δ) e he hover hagree
  refine ⟨T,hT,hT.symm,?_,?_⟩
  · intro j x
    rw [hvalue]
    change (Cδ j ((C j).symm (C j x)) : E) = Cδ j x
    rw [(C j).symm_apply_apply]
  · intro x
    obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
    have hTx : (T x : E) = e j ⟨x,hj⟩ := hvalue j ⟨x,hj⟩
    have hxP : (x : E) ∈ K.space \ g ⁻¹' S :=
      ⟨K.convexHull_subset_space j.1.1.2.1 (F.ball_subset_tetrahedron j.1.1 j.1.2
        (prismTrim_subset (H j) hj)),fun hs => disjoint_left.mp havoid x.property hs⟩
    have hyB : (T x : E) ∈ F.ball j.1.1 j.1.2 :=
      hTx ▸ prismTrimAt_subset (H j) δ (e j ⟨x,hj⟩).property
    have hyP : (T x : E) ∈ K.space \ g ⁻¹' S :=
      ⟨K.convexHull_subset_space j.1.1.2.1 (F.ball_subset_tetrahedron j.1.1 j.1.2 hyB),
        fun hs => disjoint_left.mp havoidδ (T x).property hs⟩
    have hclass := F.component_class hgi j.1.1 j.1.2 ⟨x,hxP⟩ ⟨T x,hyP⟩
      (prismTrim_subset (H j) hj) hyB
    exact (connectedComponentIn_eq ((Topology.mem_componentIn_iff_component_class hxP hyP).mpr hclass)).symm

end PoincareConjecture.M76.PrismBelt
