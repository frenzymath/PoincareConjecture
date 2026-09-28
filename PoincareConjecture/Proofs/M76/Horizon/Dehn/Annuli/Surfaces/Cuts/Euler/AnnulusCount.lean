import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.CircleCapEulerCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.SquareAnnulusCylinder
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionCylinderEulerCount



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Band" => squareAnnulus 1 (1 / 8 : ℝ)

private theorem exists_compression_cylinder_coordinates :
    ∃ H : Band ≃ₜ CompressionCylinder.carrier, H.IsFinitePL := by
  obtain ⟨C, hC, _⟩ := exists_finitePL_square_annulus_cylinder
  obtain ⟨F, hF, hFv⟩ := hC
  let scale : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  have hscalev (x : V2 × ℝ) : scale x = (x.1, x.2 / 2) := by
    change (x.1, (1 / 2 : ℝ) * x.2) = _
    congr 1
    ring
  have hscalei : Function.Injective scale := by
    intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    rw [hscalev, hscalev] at h1 h2
    refine Prod.ext (show x.1 = y.1 from h1) ?_
    dsimp at h2
    linarith
  have hFi : InjOn F Band := by
    intro x hx y hy h
    exact congrArg Subtype.val (C.injective (Subtype.ext
      ((hFv ⟨x, hx⟩).trans (h.trans (hFv ⟨y, hy⟩).symm))))
  have himage : (scale ∘ F) '' Band = CompressionCylinder.carrier := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Function.comp_apply, ← hFv ⟨x, hx⟩, hscalev]
      have h := (C ⟨x, hx⟩).property
      exact ⟨h.1, by constructor <;> linarith [h.2.1, h.2.2]⟩
    · intro hy
      have ht : (y.1, 2 * y.2) ∈ Cyl :=
        ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
      let x := C.symm ⟨(y.1, 2 * y.2), ht⟩
      have hx : F x = (y.1, 2 * y.2) :=
        (hFv x).symm.trans (congrArg Subtype.val (C.apply_symm_apply _))
      refine ⟨x, x.property, ?_⟩
      rw [Function.comp_apply, hx, hscalev]
      refine Prod.ext rfl ?_
      dsimp
      ring
  obtain ⟨H, hH, _⟩ := (hF.postcomp scale).exists_homeomorph_image
    (fun x hx y hy h ↦ hFi hx hy (hscalei h))
  exact ⟨H.trans (Homeomorph.setCongr himage), hH.setCongr rfl himage⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem annulus_surfaceEulerCount (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (c : Band ≃ₜ K.space) (hc : c.IsFinitePL) : K.surfaceEulerCount = 0 := by
  obtain ⟨H, hH⟩ := exists_compression_cylinder_coordinates
  let G := H.symm.trans c
  obtain ⟨g, hg, hgv⟩ := hH.symm.trans hc
  obtain ⟨S, hS, hSs, hSg⟩ := hg
  have hf : FinitePiecewiseAffineOn g S.space := ⟨S, hS, rfl, hSg⟩
  have hinj : InjOn g S.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hgv ⟨x, hSs.subset hx⟩).trans
        (hxy.trans (hgv ⟨y, hSs.subset hy⟩).symm))))
  have himage : g '' S.space = K.space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hgv ⟨x, hSs.subset hx⟩]
      exact (G ⟨x, hSs.subset hx⟩).property
    · intro hy
      let x := G.symm ⟨y, hy⟩
      exact ⟨x, hSs.symm.subset x.property, (hgv x).symm.trans
        (congrArg Subtype.val (G.apply_symm_apply _))⟩
  have hdim := CompressionCylinder.face_card_le_three S hSs.subset
  have htarget := hf.face_card_le_of_image hS hdim K himage.symm.subset
  exact (hf.surfaceEulerCount_eq_of_injOn hS hK hdim htarget hinj himage).symm.trans
    (CompressionCylinder.surfaceEulerCount_eq_zero S hS hSs)

end PoincareConjecture.M76.Dehn.Annuli
