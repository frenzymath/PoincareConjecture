import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberReflection



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem OriginalFaceRectangles.side_ball_from_marked_chart
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (k : D.Region)
    (G : Square ≃ₜ D.carrier k)
    (hW : ∀ x, (G x : E) ∈ D.arc (D.cap k false) ↔ (x : ℝ × ℝ).2 = 0)
    (hZ : ∀ x, (G x : E) ∈ D.arc (D.cap k true) ↔ (x : ℝ × ℝ).2 = 1)
    (hL : ∀ b x, (G x : E) ∈ D.side k b ↔ (x : ℝ × ℝ).1 = if b then 1 else 0)
    (b : Bool) :
    IsFinitePLBallPair ℝ (D.side k b) {(G (sidePoint b 0) : E),(G (sidePoint b 1) : E)} := by
  obtain ⟨p,_,hside,_,hcorner⟩ := D.exists_corner_models k
  have h0 : (G (sidePoint b 0) : E) = p b false :=
    (hcorner false b).subset ⟨(hW _).mpr rfl,(hL b _).mpr rfl⟩
  have h1 : (G (sidePoint b 1) : E) = p b true :=
    (hcorner true b).subset ⟨(hZ _).mpr rfl,(hL b _).mpr rfl⟩
  rw [h0,h1]
  exact hside b

theorem prismFiberReflection_on_affine_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B M : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip b : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (hside : ∀ t, (G (sidePoint b t) : E) =
      AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (t : ℝ))
    (t : I) :
    (prismFiberReflection H ⟨G (sidePoint b t),hMB (G _).property⟩ : E) =
      (G (sidePoint b 0) : E) + G (sidePoint b 1) - G (sidePoint b t) := by
  have href : (prismFiberReflection H ⟨G (sidePoint b t),hMB (G _).property⟩ : E) =
      G (sidePoint b (unitInterval.symm t)) := by
    cases b
    · exact prismFiberReflection_on_global_rectangle H G hMB flip hformula 0 t
    · exact prismFiberReflection_on_global_rectangle H G hMB flip hformula 1 t
  rw [href,hside (unitInterval.symm t)]
  conv_rhs => rw [hside t]
  change AffineMap.lineMap _ _ (1-(t : ℝ)) = _
  simp only [AffineMap.lineMap_apply_module,sub_smul,one_smul]
  abel

theorem prismFiberReflection_agrees_on_equal_affine_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A B M L : Bool → Set E)
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (G : ∀ i, Square ≃ₜ M i) (hMB : ∀ i, M i ⊆ B i) (flip side : Bool → Bool)
    (hformula : ∀ i (u t : I),
      ((H i).symm ⟨G i ⟨(u,fiberFlip (flip i) t),u.property,(fiberFlip (flip i) t).property⟩,
        hMB i (G i _).property⟩ : E × ℝ) =
        ((G i ⟨(u,fiberFlip (flip i) 0),u.property,(fiberFlip (flip i) 0).property⟩ : E),(t : ℝ)))
    (hside : ∀ i t, (G i (sidePoint (side i) t) : E) =
      AffineMap.lineMap (G i (sidePoint (side i) 0) : E) (G i (sidePoint (side i) 1) : E) (t : ℝ))
    (hball : ∀ i, IsFinitePLBallPair ℝ (L i)
      {(G i (sidePoint (side i) 0) : E),(G i (sidePoint (side i) 1) : E)})
    (hL : L false = L true)
    (t s : I) (hpoint : (G false (sidePoint (side false) t) : E) =
      G true (sidePoint (side true) s)) :
    (prismFiberReflection (H false)
      ⟨G false (sidePoint (side false) t),hMB false (G false _).property⟩ : E) =
      prismFiberReflection (H true)
        ⟨G true (sidePoint (side true) s),hMB true (G true _).property⟩ := by
  have hball' := hball false
  rw [hL] at hball'
  have hpairs := hball'.boundary_eq_of_same_carrier (hball true)
  have hsum : (G false (sidePoint (side false) 0) : E) + G false (sidePoint (side false) 1) =
      (G true (sidePoint (side true) 0) : E) + G true (sidePoint (side true) 1) := by
    rcases pair_eq_pair_iff.mp hpairs with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · rw [h0,h1]
    · rw [h0,h1,add_comm]
  rw [prismFiberReflection_on_affine_side (H false) (G false) (hMB false)
    (flip false) (side false) (hformula false) (hside false),
    prismFiberReflection_on_affine_side (H true) (G true) (hMB true)
      (flip true) (side true) (hformula true) (hside true),hsum,hpoint]

end PoincareConjecture.M76.PrismBelt
