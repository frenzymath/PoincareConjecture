import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Mathlib.RelativePolyhedralNeighborhood

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem polyhedralPLInCharts_carrier_inclusion
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Set E} (e : ι → OpenPartialHomeomorph W V3)
    (hcover : ∀ x : W, ∃ i, x ∈ (e i).source)
    (hrep : ∀ i, ∃ (A : Set E) (g : E → V3), FinitePiecewiseAffineOn g A ∧
      ∀ x ∈ (e i).source, (x : E) ∈ A ∧ e i x = g x)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → W)
    (hval : ∀ x ∈ K.space, (f x : E) = x) :
    PolyhedralPLInCharts e f K.space := by
  have hfc : Continuous (fun x : K.space => f x) := by
    apply continuous_induced_rng.mpr
    convert (continuous_subtype_val : Continuous (fun x : K.space => (x : E))) using 1
    funext x
    exact hval x x.property
  refine ⟨continuousOn_iff_continuous_domRestrict.mpr hfc,?_⟩
  intro x
  obtain ⟨i,hi⟩ := hcover (f x)
  let O : Set K.space := (fun y => f y) ⁻¹' (e i).source
  have hO : IsOpen O := (e i).open_source.preimage hfc
  obtain ⟨J,V,hJ,hJK,hV,hxV,hVJ,hJO⟩ := K.exists_relative_polyhedral_neighborhood hK x hO hi
  have hmap : MapsTo f J.space (e i).source :=
    fun y hy => hJO (show (⟨y,hJK hy⟩ : K.space) ∈ Subtype.val ⁻¹' J.space from hy)
  obtain ⟨A,g,hg,hgv⟩ := hrep i
  have hJA : J.space ⊆ A := by
    intro y hy
    simpa only [hval y (hJK hy)] using (hgv (f y) (hmap hy)).1
  refine ⟨i,J,V,hJ,hJK,hV,hxV,hVJ,hmap,?_⟩
  apply (hg.restrict J hJ hJA).congr
  intro y hy
  change g y = e i (f y)
  rw [(hgv (f y) (hmap hy)).2,hval y (hJK hy)]

theorem exists_chartwisePLBall_in_carrier
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W D B : Set E} (e : ι → OpenPartialHomeomorph W V3)
    (hcover : ∀ x : W, ∃ i, x ∈ (e i).source)
    (hrep : ∀ i, ∃ (A : Set E) (g : E → V3), FinitePiecewiseAffineOn g A ∧
      ∀ x ∈ (e i).source, (x : E) ∈ A ∧ e i x = g x)
    (hD : IsFinitePLBallPair V3 D B) (hDW : D ⊆ W) :
    Nonempty (ChartwisePLBall e ((Subtype.val : W → E) ⁻¹' D)
      ((Subtype.val : W → E) ⁻¹' B)) := by
  classical
  obtain ⟨p,hp,_⟩ := hD.sdiff_nonempty
  let f : E → W := fun x => if hx : x ∈ W then ⟨x,hx⟩ else ⟨p,hDW hp⟩
  have hval (x : E) (hx : x ∈ D) : (f x : E) = x := by
    simp only [f,dif_pos (hDW hx)]
  have hcopy := hD
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hcopy
  have hf : PolyhedralPLInCharts e f D := by
    rw [←hKs]
    exact polyhedralPLInCharts_carrier_inclusion e hcover hrep K hK f
      (fun x hx => hval x (hKs.subset hx))
  have hfi : InjOn f D := by
    intro x hx y hy hxy
    simpa only [hval x hx,hval y hy] using congrArg Subtype.val hxy
  have him (A : Set E) (hAD : A ⊆ D) : f '' A = (Subtype.val : W → E) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (f y : E) ∈ A
      rwa [hval y (hAD hy)]
    · intro hx
      refine ⟨x,hx,Subtype.ext (hval x (hAD hx))⟩
  simpa only [him D subset_rfl,him B hD.1] using
    exists_chartwisePLBall_image hD (ContinuousLinearEquiv.refl ℝ V3) hf subset_rfl hfi

end PoincareConjecture.M76
