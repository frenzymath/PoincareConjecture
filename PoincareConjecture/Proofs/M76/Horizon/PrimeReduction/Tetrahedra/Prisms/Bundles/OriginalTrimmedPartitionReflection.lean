import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCutBallFiberAgreement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularBallCutContact
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.TrimmedFiberReflection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "V3" => (Fin 3 → ℝ)
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def RegularOriginalCutCell
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (S : Set X)
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (κ : K.FaceOfCard 4 → Type*) (B : ∀ t, κ t → Set E) :=
  {j : Σ t, κ t // ∀ (f : TetrahedronFace K j.1.1)
    (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f.1).arc i : Set E)),
    (x : E) ∈ B j.1 j.2 → ConnectedComponents.mk x ∉ (D f.1).exceptional}

set_option maxHeartbeats 600000 in
theorem exists_original_trimmed_partition_reflection
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hG : ∀ s k, (G s k).IsFinitePL)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (ι κ : K.FaceOfCard 4 → Type*) [∀ t, Finite (ι t)] [∀ t, Finite (κ t)]
    (cut rim : ∀ t, ι t → Set E)
    (hcut : ∀ t i, IsFinitePLBallPair (ℝ × ℝ) (cut t i) (rim t i))
    (hsub : ∀ t i, cut t i ⊆ convexHull ℝ (t.1 : Set E))
    (hrim : ∀ t i, cut t i ∩ intrinsicFrontier ℝ (convexHull ℝ (t.1 : Set E)) = rim t i)
    (hdis : ∀ t, Pairwise fun i j => Disjoint (cut t i) (cut t j))
    (hphysical : ∀ t, g '' (⋃ i, cut t i) = S ∩ (g '' convexHull ℝ (t.1 : Set E)))
    (B R : ∀ t, κ t → Set E)
    (hB : ∀ t k, IsFinitePLBallPair V3 (B t k) (R t k))
    (hR : ∀ t k, R t k = B t k ∩ (intrinsicFrontier ℝ (convexHull ℝ (t.1 : Set E)) ∪ ⋃ i, cut t i))
    (hcover : ∀ t, (⋃ k, B t k) = convexHull ℝ (t.1 : Set E))
    (hinter : ∀ t, Pairwise (fun k l => B t k ∩ B t l ⊆ ⋃ i, cut t i))
    (hwhole : ∀ t k i, (B t k ∩ cut t i).Nonempty → cut t i ⊆ R t k)
    (hcomp : ∀ t k x, x ∈ B t k \ ⋃ i, cut t i →
      connectedComponentIn (convexHull ℝ (t.1 : Set E) \ ⋃ i, cut t i) x = B t k \ ⋃ i, cut t i) :
    let Cell := RegularOriginalCutCell K g S D κ B
    ∃ (i₀ i₁ : ∀ j : Cell, ι j.1.1),
      (∀ j, i₀ j ≠ i₁ j) ∧
      (∀ j, cut j.1.1 (i₀ j) ⊆ R j.1.1 j.1.2 ∧ cut j.1.1 (i₁ j) ⊆ R j.1.1 j.1.2) ∧
    ∃ flip : ∀ j : Cell,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (B j.1.1 j.1.2) → Bool,
    ∃ H : ∀ j : Cell, (cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ B j.1.1 j.1.2,
      (∀ j, (H j).IsFinitePL) ∧
      (∀ j x, (H j x : E) ∈ cut j.1.1 (i₀ j) ↔ (x : E × ℝ).2 = 0) ∧
      (∀ j x, (H j x : E) ∈ cut j.1.1 (i₁ j) ↔ (x : E × ℝ).2 = 1) ∧
      (∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
        (B j.1.1 j.1.2)) (u t : I),
        ((H j).symm ⟨G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
          z.2 (G _ _ _).property⟩ : E × ℝ) =
          ((G z.1.1.1 z.1.2
            ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ))) ∧
    ∃ C : ∀ j : Cell, (cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j),
      (∀ j, (C j).IsFinitePL) ∧
      (∀ j x, (C j x : E) = H j (trimProduct (cut j.1.1 (i₀ j)) x)) ∧
      Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S) ∧
    ∃ J : (⋃ j, prismTrim (H j)) ≃ₜ (⋃ j, prismTrim (H j)),
      J.IsFinitePL ∧ Function.Involutive J ∧
      (∀ j (x : prismTrim (H j)),
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberReflection (C j) x) ∧
      ∀ j (x : prismTrim (H j)),
        (((C j).symm x : E × ℝ).2 = 0 ∨ ((C j).symm x : E × ℝ).2 = 1) →
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) ≠ x := by
  classical
  dsimp only
  let Cell := RegularOriginalCutCell K g S D κ B
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI : Finite Cell := by
    dsimp [Cell,RegularOriginalCutCell]
    infer_instance
  have hBsub (t : K.FaceOfCard 4) (k : κ t) : B t k ⊆ convexHull ℝ (t.1 : Set E) :=
    fun _ hx => (hcover t).subset (mem_iUnion.mpr ⟨k,hx⟩)
  have hphysical' (t : K.FaceOfCard 4) (x : E) (hx : x ∈ convexHull ℝ (t.1 : Set E)) :
      x ∈ (⋃ i, cut t i) ↔ g x ∈ S :=
    original_face_cut_mem_iff K g hgi t.2.1 (iUnion_subset (hsub t)) (hphysical t) hx
  have hglobal (t : K.FaceOfCard 4) : (convexHull ℝ (t.1 : Set E) \ g ⁻¹' S : Set E) =
      convexHull ℝ (t.1 : Set E) \ ⋃ i, cut t i := by
    ext x
    exact and_congr_right (fun hx => not_congr (hphysical' t x hx).symm)
  have hlocal (t : K.FaceOfCard 4) (k : κ t) : (B t k \ g ⁻¹' S : Set E) = B t k \ ⋃ i, cut t i := by
    ext x
    exact and_congr_right (fun hx => not_congr (hphysical' t x (hBsub t k hx)).symm)
  have hcomp' (t : K.FaceOfCard 4) (k : κ t) (x : E) (hx : x ∈ B t k \ g ⁻¹' S) :
      connectedComponentIn (convexHull ℝ (t.1 : Set E) \ g ⁻¹' S) x = B t k \ g ⁻¹' S := by
    rw [hglobal,hlocal]
    exact hcomp t k x ((hlocal t k).subset hx)
  have hex (j : Cell) := exists_actual_global_cut_ball_prism K hK g hgi j.1.1.2.1 j.1.1.2.2
    (fun f => D f.1)
    (cut j.1.1) (rim j.1.1) (hcut j.1.1) (hsub j.1.1) (hrim j.1.1)
    (hdis j.1.1) (hphysical j.1.1) (hB j.1.1 j.1.2) (hR j.1.1 j.1.2)
    (hwhole j.1.1 j.1.2) (hcomp' j.1.1 j.1.2) j.2
    (fun z => G z.1.1.1 z.1.2) (fun z => hG _ _) (fun z => hW _ _)
    (fun z => hZ _ _) (fun z => hL _ _) (fun z => haffine _ _)
  choose i₀ i₁ hne hi₀ hi₁ flip H hH hHid hH0 hH1 hHM hformula using hex
  choose C hC hCv using fun j => exists_finitePL_symmetric_prism_trim (H j) (hH j)
  have havoidCut (j : Cell) : Disjoint (prismTrim (H j)) (⋃ i, cut j.1.1 i) := by
    have hcontact := original_regular_ball_cut_contact K hK g hgi j.1.1.2.1 j.1.1.2.2
      (fun f => D f.1) (cut j.1.1) (rim j.1.1) (hcut j.1.1) (hsub j.1.1)
      (hrim j.1.1) (hdis j.1.1) (hphysical j.1.1) (hB j.1.1 j.1.2) (hR j.1.1 j.1.2)
      (hwhole j.1.1 j.1.2) (hcomp' j.1.1 j.1.2) j.2 (i₀ j) (i₁ j) (hne j) (hi₀ j) (hi₁ j)
    exact prismTrim_disjoint_total_cut (H j) (cut j.1.1) (i₀ j) (i₁ j) hcontact (hH0 j) (hH1 j)
  have havoid (j : Cell) : Disjoint (prismTrim (H j)) (g ⁻¹' S) :=
    prismTrim_disjoint_physical_cut K g hgi j.1.1.2.1 (H j) (hBsub j.1.1 j.1.2)
      (cut j.1.1) (iUnion_subset (hsub j.1.1)) (hphysical j.1.1) (havoidCut j)
  let e (j : Cell) := prismFiberReflection (C j)
  have he (j : Cell) : (e j).IsFinitePL :=
    prismFiberReflection_finitePL (hcut j.1.1 (i₀ j)) (C j) (hC j)
  have hinv (j : Cell) : Function.Involutive (e j) := prismFiberReflection_involutive (C j)
  have hagree (j l : Cell) (x : E) (hj : x ∈ prismTrim (H j)) (hl : x ∈ prismTrim (H l)) :
      (e j ⟨x,hj⟩ : E) = e l ⟨x,hl⟩ := by
    by_cases hsame : j = l
    · subst l
      rfl
    have hxj := prismTrim_subset (H j) hj
    have hxl := prismTrim_subset (H l) hl
    by_cases ht : j.1.1 = l.1.1
    · exfalso
      rcases j with ⟨⟨t,k⟩,hjreg⟩
      rcases l with ⟨⟨u,m⟩,hlreg⟩
      dsimp only at ht
      subst u
      have hkm : k ≠ m := fun h => hsame (Subtype.ext (by subst m; rfl))
      exact disjoint_left.mp (havoidCut ⟨⟨t,k⟩,hjreg⟩) hj ((hinter t hkm) ⟨hxj,hxl⟩)
    · let p : Bool → Cell := Bool.rec j l
      have htet : (p false).1.1.1 ≠ (p true).1.1.1 := fun h => ht (Subtype.ext h)
      have href := original_cut_ball_prism_fibers_agree K g hgi D G hW hZ hL haffine
        (fun b => (p b).1.1.1) (fun b => (p b).1.1.2.1) (fun b => (p b).1.1.2.2) htet
        (fun b => cut (p b).1.1 (i₀ (p b))) (fun b => B (p b).1.1 (p b).1.2)
        (fun b => (hB (p b).1.1 (p b).1.2).isCompact.isClosed)
        (fun b => hBsub (p b).1.1 (p b).1.2) (fun b => hcomp' (p b).1.1 (p b).1.2)
        (fun b => (p b).2) (fun b => H (p b)) (fun b => flip (p b))
        (fun b => hformula (p b)) ⟨hxj,hxl⟩ (fun hx => disjoint_left.mp (havoid j) hj hx)
      exact (prismFiberReflection_trim_chart (H j) (C j) (hCv j) ⟨x,hj⟩).trans
        (href.1.trans (prismFiberReflection_trim_chart (H l) (C l) (hCv l) ⟨x,hl⟩).symm)
  have hmaps (j l : Cell) (x : prismTrim (H j)) (hx : (x : E) ∈ prismTrim (H l)) :
      (e j x : E) ∈ prismTrim (H l) :=
    (hagree j l x x.property hx).symm ▸ (e l ⟨x,hx⟩).property
  have hover (j l : Cell) (x : prismTrim (H j)) :
      (x : E) ∈ prismTrim (H l) ↔ (e j x : E) ∈ prismTrim (H l) := by
    refine ⟨hmaps j l x,?_⟩
    intro hx
    simpa only [hinv j x] using hmaps j l (e j x) hx
  obtain ⟨J,hJ,hvalue⟩ := Homeomorph.exists_iUnion_finitePL
    (fun j => prismTrim (H j)) (fun j => prismTrim (H j)) e he hover hagree
  refine ⟨i₀,i₁,hne,fun j => ⟨hi₀ j,hi₁ j⟩,flip,H,hH,hH0,hH1,hformula,C,hC,hCv,?_,J,hJ,?_,hvalue,?_⟩
  · exact disjoint_iUnion_left.mpr havoid
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
