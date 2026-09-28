import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.VariableSymmetricPrismTrim
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularComponentCoverage

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem OriginalTetrahedralCutFamily.regular_ball_cut_contact
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite) {g : E → X} (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (F : OriginalTetrahedralCutFamily K g S)
    (j : RegularOriginalCutCell K g S D F.BallIndex F.ball)
    (i₀ i₁ : F.DiskIndex j.1.1) (hne : i₀ ≠ i₁)
    (h₀ : F.cut j.1.1 i₀ ⊆ F.boundary j.1.1 j.1.2)
    (h₁ : F.cut j.1.1 i₁ ⊆ F.boundary j.1.1 j.1.2) :
    F.ball j.1.1 j.1.2 ∩ g ⁻¹' S = F.cut j.1.1 i₀ ∪ F.cut j.1.1 i₁ := by
  classical
  letI := F.finite_disk j.1.1
  have hc := original_regular_ball_cut_contact K hK g hgi j.1.1.2.1 j.1.1.2.2
    (fun f => D f.1) (F.cut j.1.1) (F.rim j.1.1) (F.disk_pair j.1.1)
    (F.disk_subset j.1.1) (F.disk_frontier j.1.1) (F.disk_disjoint j.1.1)
    (F.physical j.1.1) (F.ball_pair j.1.1 j.1.2) (F.ball_frontier j.1.1 j.1.2)
    (F.whole_disk j.1.1 j.1.2) (fun _ hx => F.component_physical hgi j.1.1 j.1.2 hx)
    j.2 i₀ i₁ hne h₀ h₁
  rw [← hc]
  ext x
  exact and_congr_right (fun hx => (F.mem_cut_iff_physical hgi j.1.1
    (F.ball_subset_tetrahedron j.1.1 j.1.2 hx)).symm)

set_option maxHeartbeats 600000 in
theorem exists_original_variable_trimmed_reflection
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
    (i₀ i₁ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (hne : ∀ j, i₀ j ≠ i₁ j)
    (hcap : ∀ j, F.cut j.1.1 (i₀ j) ⊆ F.boundary j.1.1 j.1.2 ∧
      F.cut j.1.1 (i₁ j) ⊆ F.boundary j.1.1 j.1.2)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (hH : ∀ j, (H j).IsFinitePL)
    (hzero : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₀ j) ↔ (y : E × ℝ).2 = 0)
    (hone : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₁ j) ↔ (y : E × ℝ).2 = 1)
    (flip : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (F.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (F.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    ∃ C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt (H j) δ,
      (∀ j, (C j).IsFinitePL) ∧
      (∀ j x, (C j x : E) = H j (trimProductAt (F.cut j.1.1 (i₀ j)) δ hδ hhalf x)) ∧
      Disjoint (⋃ j, prismTrimAt (H j) δ) (g ⁻¹' S) ∧
    ∃ J : (⋃ j, prismTrimAt (H j) δ) ≃ₜ (⋃ j, prismTrimAt (H j) δ),
      J.IsFinitePL ∧ Function.Involutive J ∧
      (∀ j (x : prismTrimAt (H j) δ),
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberReflection (C j) x) ∧
      ∀ j (x : prismTrimAt (H j) δ),
        (((C j).symm x : E × ℝ).2 = 0 ∨ ((C j).symm x : E × ℝ).2 = 1) →
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) ≠ x := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite Cell := by dsimp [Cell,RegularOriginalCutCell]; infer_instance
  choose C hC hCv using fun j : Cell => exists_finitePL_prism_trim_at (H j) (hH j) δ hδ hhalf
  have havoid (j : Cell) : Disjoint (prismTrimAt (H j) δ) (g ⁻¹' S) := by
    apply disjoint_left.mpr
    intro x hx hxS
    have hc := F.regular_ball_cut_contact hK hgi D j (i₀ j) (i₁ j) (hne j) (hcap j).1 (hcap j).2
    exact disjoint_left.mp (prismTrimAt_disjoint_caps (H j) (hzero j) (hone j) δ hδ) hx
      (hc.subset ⟨prismTrimAt_subset (H j) δ hx,hxS⟩)
  let e (j : Cell) := prismFiberReflection (C j)
  have he (j : Cell) : (e j).IsFinitePL :=
    prismFiberReflection_finitePL (F.disk_pair j.1.1 (i₀ j)) (C j) (hC j)
  have hinv (j : Cell) : Function.Involutive (e j) := prismFiberReflection_involutive (C j)
  have hagree (j l : Cell) (x : E) (hj : x ∈ prismTrimAt (H j) δ) (hl : x ∈ prismTrimAt (H l) δ) :
      (e j ⟨x,hj⟩ : E) = e l ⟨x,hl⟩ := by
    by_cases hsame : j = l
    · subst l
      rfl
    have hxj := prismTrimAt_subset (H j) δ hj
    have hxl := prismTrimAt_subset (H l) δ hl
    have hxS : g x ∉ S := fun hs => disjoint_left.mp (havoid j) hj hs
    by_cases ht : j.1.1 = l.1.1
    · exfalso
      rcases j with ⟨⟨t,k⟩,hjreg⟩
      rcases l with ⟨⟨u,n⟩,hlreg⟩
      dsimp only at ht
      subst u
      have hkn : k ≠ n := fun h => hsame (Subtype.ext (by subst n; rfl))
      exact hxS ((F.mem_cut_iff_physical hgi t (F.ball_subset_tetrahedron t k hxj)).mp
        ((F.intersection t hkn) ⟨hxj,hxl⟩))
    · let p : Bool → Cell := Bool.rec j l
      have htet : (p false).1.1.1 ≠ (p true).1.1.1 := fun h => ht (Subtype.ext h)
      have href := original_cut_ball_prism_fibers_agree K g hgi D G hW hZ hL haffine
        (fun b => (p b).1.1.1) (fun b => (p b).1.1.2.1) (fun b => (p b).1.1.2.2) htet
        (fun b => F.cut (p b).1.1 (i₀ (p b))) (fun b => F.ball (p b).1.1 (p b).1.2)
        (fun b => (F.ball_pair (p b).1.1 (p b).1.2).isCompact.isClosed)
        (fun b => F.ball_subset_tetrahedron (p b).1.1 (p b).1.2)
        (fun b _ hx => F.component_physical hgi (p b).1.1 (p b).1.2 hx)
        (fun b => (p b).2) (fun b => H (p b)) (fun b => flip (p b))
        (fun b => hformula (p b)) ⟨hxj,hxl⟩ hxS
      exact (prismFiberReflection_trimAt_chart (H j) δ hδ hhalf (C j) (hCv j) ⟨x,hj⟩).trans
        (href.1.trans (prismFiberReflection_trimAt_chart (H l) δ hδ hhalf (C l) (hCv l) ⟨x,hl⟩).symm)
  have hmaps (j l : Cell) (x : prismTrimAt (H j) δ) (hx : (x : E) ∈ prismTrimAt (H l) δ) :
      (e j x : E) ∈ prismTrimAt (H l) δ :=
    (hagree j l x x.property hx).symm ▸ (e l ⟨x,hx⟩).property
  have hover (j l : Cell) (x : prismTrimAt (H j) δ) :
      (x : E) ∈ prismTrimAt (H l) δ ↔ (e j x : E) ∈ prismTrimAt (H l) δ := by
    refine ⟨hmaps j l x,?_⟩
    intro hx
    simpa only [hinv j x] using hmaps j l (e j x) hx
  obtain ⟨J,hJ,hvalue⟩ := Homeomorph.exists_iUnion_finitePL
    (fun j => prismTrimAt (H j) δ) (fun j => prismTrimAt (H j) δ) e he hover hagree
  refine ⟨C,hC,hCv,disjoint_iUnion_left.mpr havoid,J,hJ,?_,hvalue,?_⟩
  · intro x
    obtain ⟨j,hxj⟩ := mem_iUnion.mp x.property
    have hx : (J x : E) = e j ⟨x,hxj⟩ := hvalue j ⟨x,hxj⟩
    apply Subtype.ext
    calc
      (J (J x) : E) = J ⟨e j ⟨x,hxj⟩,mem_iUnion.mpr ⟨j,(e j ⟨x,hxj⟩).property⟩⟩ :=
        congrArg (fun y => (J y : E)) (Subtype.ext hx)
      _ = e j (e j ⟨x,hxj⟩) := hvalue j _
      _ = x := congrArg Subtype.val (hinv j ⟨x,hxj⟩)
  · intro j x hend heq
    have hfix : prismFiberReflection (C j) x = x := Subtype.ext ((hvalue j x).symm.trans heq)
    have hhalf := (prismFiberReflection_eq_iff_height (C j) x).mp hfix
    rcases hend with hend | hend <;> linarith

end PoincareConjecture.M76.PrismBelt
