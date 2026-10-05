import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.Belts.RectangleCornerModels

/-! # Exact finite PL interval charts extracted from a prescribed rectangle -/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_prescribed_rectangle_side_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M L : Set E} (G : Square ≃ₜ M) (hG : G.IsFinitePL) (hLM : L ⊆ M) (k : I)
    (hL : ∀ z, (G z : E) ∈ L ↔ (z : ℝ × ℝ).1 = k) :
    ∃ d : I ≃ₜ L, d.IsFinitePL ∧
      ∀ t : I, (d t : E) = G ⟨(k,t),k.property,t.property⟩ := by
  obtain ⟨f,hf,hfG⟩ := hG
  let a : ℝ →ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousAffineMap.const ℝ ℝ (k : ℝ)).prod (ContinuousAffineMap.id ℝ ℝ)
  obtain ⟨K,_,hK,hKs,_,_⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).exists_finite_carrier_and_rim_complexes
  have ha : FinitePiecewiseAffineOn a I := ⟨K,hK,hKs,K.affineOnFaces_affine a⟩
  have hfa : FinitePiecewiseAffineOn (f ∘ a) I :=
    hf.comp ha (fun x hx => ⟨k.property,hx⟩)
  have hval (t : I) : (f ∘ a) t = (G ⟨(k,t),k.property,t.property⟩ : E) :=
    (hfG ⟨(k,t),k.property,t.property⟩).symm
  have hi : InjOn (f ∘ a) I := by
    intro x hx y hy he
    have hg : G ⟨(k,x),k.property,hx⟩ = G ⟨(k,y),k.property,hy⟩ :=
      Subtype.ext ((hval ⟨x,hx⟩).symm.trans (he.trans (hval ⟨y,hy⟩)))
    exact congrArg (fun z : Square => (z : ℝ × ℝ).2) (G.injective hg)
  have himage : (f ∘ a) '' I = L := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      rw [hval ⟨t,ht⟩]
      exact (hL _).mpr rfl
    · intro hx
      let z := G.symm ⟨x,hLM hx⟩
      have hz : (G z : E) = x := congrArg Subtype.val (G.apply_symm_apply _)
      have hk : (z : ℝ × ℝ).1 = k := (hL z).mp (hz.symm ▸ hx)
      refine ⟨(z : ℝ × ℝ).2,z.property.2,?_⟩
      have he : (⟨(k,(z : ℝ × ℝ).2),k.property,z.property.2⟩ : Square) = z :=
        Subtype.ext (Prod.ext hk.symm rfl)
      exact (hval ⟨_,z.property.2⟩).trans
        ((congrArg (fun w : Square => (G w : E)) he).trans hz)
  have hex := hfa.exists_homeomorph_image hi
  rw [himage] at hex
  obtain ⟨d,hd,hdval⟩ := hex
  exact ⟨d,hd,fun t => (hdval t).trans (hval t)⟩

end PoincareMT.M76.PrismBelt
