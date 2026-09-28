import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E G ι : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem exists_compact_finitePL_image_neighborhood
    (e : ι → OpenPartialHomeomorph M E) (F : M → G) (hF : Continuous F)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    {A U : Set M} (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    (hinj : InjOn F U) :
    ∃ (C : Set M) (K : SimplicialComplex ℝ G) (H : C ≃ₜ K.space),
      IsCompact C ∧ A ⊆ interior C ∧ C ⊆ U ∧ K.faces.Finite ∧
      K.space = F '' C ∧ ∀ x : C, (H x : G) = F x := by
  classical
  have hchoose (x : A) : ∃ (i : ι) (L : SimplicialComplex ℝ E),
      (x : M) ∈ (e i).source ∧ L.faces.Finite ∧
      e i x ∈ interior L.space ∧ L.space ⊆ (e i).target ∧
      MapsTo (e i).symm L.space U ∧ L.AffineOnFaces (F ∘ (e i).symm) := by
    obtain ⟨i, hxi⟩ := hcover x
    obtain ⟨J, hJ, hxJ, _, hFJ⟩ := hFPL i (e i x) ((e i).mapsTo hxi)
    let V : Set E := (e i).target ∩ (e i).symm ⁻¹' U
    have hV : IsOpen V :=
      (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    have hxV : e i x ∈ V := by
      refine ⟨(e i).mapsTo hxi, ?_⟩
      change (e i).symm (e i x) ∈ U
      rw [(e i).left_inv hxi]
      exact hAU x.property
    obtain ⟨L, hL, hxL, hLV, hFL⟩ :=
      hFJ.exists_finite_neighborhood hJ (isCompact_singleton (x := e i x)) hV
        (singleton_subset_iff.mpr ⟨hxJ, hxV⟩)
    exact ⟨i, L, hxi, hL, hxL (mem_singleton _),
      fun y hy => (hLV hy).2.1, fun y hy => (hLV hy).2.2, hFL⟩
  choose c L hc hL hxL hLt hLU hFL using hchoose
  have hlocalinj (x : A) : InjOn (F ∘ (e (c x)).symm) (L x).space := by
    intro y hy z hz hyz
    exact (e (c x)).symm.injOn (hLt x hy) (hLt x hz)
      (hinj (hLU x hy) (hLU x hz) hyz)
  let J : A → SimplicialComplex ℝ G := fun x => (hFL x).embeddedImage (hlocalinj x)
  have hJ (x : A) : (J x).faces.Finite :=
    (hFL x).embeddedImage_finite (hlocalinj x) (hL x)
  have hJs (x : A) : (J x).space = (F ∘ (e (c x)).symm) '' (L x).space :=
    (hFL x).embeddedImage_space (hlocalinj x)
  let D : A → Set M := fun x => (e (c x)).symm '' (L x).space
  have hD (x : A) : IsCompact (D x) :=
    ((L x).isCompact_space_of_finite (hL x)).image_of_continuousOn
      ((e (c x)).symm.continuousOn.mono (hLt x))
  have hDU (x : A) : D x ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hLU x hy
  let B : A → Set M := fun x =>
    (e (c x)).source ∩ (e (c x)) ⁻¹' interior (L x).space
  have hB (x : A) : IsOpen (B x) :=
    (e (c x)).continuousOn.isOpen_inter_preimage (e (c x)).open_source isOpen_interior
  have hxB (x : A) : (x : M) ∈ B x := ⟨hc x, hxL x⟩
  have hBD (x : A) : B x ⊆ D x := by
    intro y hy
    exact ⟨e (c x) y, interior_subset hy.2, (e (c x)).left_inv hy.1⟩
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover B hB
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩)
  let C : Set M := ⋃ x : s, D x
  have hC : IsCompact C := isCompact_iUnion (fun x : s => hD x)
  have hCU : C ⊆ U := by
    intro x hx
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
    exact hDU a hxa
  have hAC : A ⊆ interior C := by
    intro x hx
    obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp (hs hx)
    have hBaC : B a ⊆ C := fun y hy => mem_iUnion.mpr ⟨⟨a, has⟩, hBD a hy⟩
    exact interior_maximal hBaC (hB a) hxa
  obtain ⟨K, hK, hKs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion
    (fun x : s => J x) (fun x => hJ x)
  have hKC : K.space = F '' C := by
    rw [hKs]
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp hz
      rw [hJs x] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨(e (c x)).symm y,
        mem_iUnion.mpr ⟨x, ⟨y, hy, rfl⟩⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      obtain ⟨y, hy, hyx⟩ := ha
      apply mem_iUnion.mpr
      refine ⟨a, ?_⟩
      rw [hJs a]
      exact ⟨y, hy, congrArg F hyx⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let H0 : C ≃ₜ F '' C := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn F C (hinj.mono hCU))
    ((hF.continuousOn : ContinuousOn F C).domRestrict.subtype_mk _)
  let H := H0.trans (Homeomorph.setCongr hKC.symm)
  exact ⟨C, K, H, hC, hAC, hCU, hK, hKC, fun _ => rfl⟩

end OpenPartialHomeomorph
