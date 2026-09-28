import PoincareConjecture.Proofs.M76.Rigidity.OriginalDomainBoundaryCollar
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.InwardCompression
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

open Classical in

structure OriginalFiniteCollarModel {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) where
  vertices : Finset R
  coordinates : X → (vertices → ℝ × V3)
  complex : SimplicialComplex ℝ (vertices → ℝ × V3)
  boundary : SimplicialComplex ℝ (vertices → ℝ × V3)
  homeomorph : R ≃ₜ complex.space
  inverse : (vertices → ℝ × V3) → R
  coordinates_continuous : Continuous coordinates
  coordinates_pl : ∀ i,
    LocallyPiecewiseAffineOn (coordinates ∘ (e i).symm) (e i).target
  finite : complex.faces.Finite
  boundary_le : boundary ≤ complex
  homeomorph_eq : ∀ x : R, (homeomorph x : vertices → ℝ × V3) = coordinates x
  inverse_eq : ∀ z : complex.space, (inverse z : X) = (homeomorph.symm z : X)
  inverse_pl : PolyhedralPLInCharts e (fun z => (inverse z : X)) complex.space
  boundary_eq : ∀ z ∈ complex.space, (inverse z : X) ∈ frontier R ↔ z ∈ boundary.space
  collarVertices : Finset R
  collarBase : SimplicialComplex ℝ (collarVertices → ℝ × V3)
  collarHomeomorph : collarBase.space ≃ₜ boundary.space
  collar : (collarVertices → ℝ × V3) × ℝ → (vertices → ℝ × V3)
  collar_finite : collarBase.faces.Finite
  collar_pl : FinitePiecewiseAffineOn collar (collarBase.space ×ˢ I)
  collar_injective : InjOn collar (collarBase.space ×ˢ I)
  collar_inside : MapsTo collar (collarBase.space ×ˢ I) complex.space
  collar_zero : ∀ z : collarBase.space,
    collar ((z : collarVertices → ℝ × V3), 0) = collarHomeomorph z
  collar_boundary : ∀ z ∈ collarBase.space ×ˢ I, collar z ∈ boundary.space ↔ z.2 = 0
  collar_open : IsOpen ((Subtype.val : complex.space → (vertices → ℝ × V3)) ⁻¹'
    (collar '' (collarBase.space ×ˢ Ico (0 : ℝ) 1)))

namespace OriginalFiniteCollarModel

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}

theorem coordinates_injective (M : OriginalFiniteCollarModel e R) :
    InjOn M.coordinates R := by
  intro x hx y hy hxy
  exact congrArg Subtype.val (M.homeomorph.injective (Subtype.ext
    ((M.homeomorph_eq ⟨x, hx⟩).trans (hxy.trans (M.homeomorph_eq ⟨y, hy⟩).symm))))

theorem coordinates_mapsTo (M : OriginalFiniteCollarModel e R) :
    MapsTo M.coordinates R M.complex.space := by
  intro x hx
  rw [← M.homeomorph_eq ⟨x, hx⟩]
  exact (M.homeomorph ⟨x, hx⟩).property

theorem inverse_coordinates (M : OriginalFiniteCollarModel e R) (x : X) (hx : x ∈ R) :
    (M.inverse (M.coordinates x) : X) = x := by
  rw [← M.homeomorph_eq ⟨x, hx⟩, M.inverse_eq, M.homeomorph.symm_apply_apply]

theorem coordinates_boundary (M : OriginalFiniteCollarModel e R) (x : X) (hx : x ∈ R) :
    M.coordinates x ∈ M.boundary.space ↔ x ∈ frontier R := by
  rw [← M.boundary_eq _ (M.coordinates_mapsTo hx), M.inverse_coordinates x hx]

end OriginalFiniteCollarModel

theorem PLDomain.nonempty_original_finite_collar_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hRne : R.Nonempty) :
    Nonempty (OriginalFiniteCollarModel e R) := by
  classical
  obtain ⟨s, phi, K, A, H, g, HA, hphi, hphiPL, hK, hAK, _, _, hKs,
    hAs, hH, _, hg, hgPL, _, hHAinv, hboundary, _⟩ :=
    he.exists_original_frontier_surface_model hR hRne
  have hphii : InjOn phi R := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))))
  have hmem (x : X) (hx : x ∈ R) : phi x ∈ A.space ↔ x ∈ frontier R := by
    rw [hAs]
    constructor
    · rintro ⟨y, hy, heq⟩
      exact hphii (he.closed.frontier_subset hy) hx heq ▸ hy
    · intro h
      exact mem_image_of_mem phi h
  have hne : (interior R).Nonempty := closure_nonempty_iff.mp
    (he.closure_interior.symm ▸ hRne)
  obtain ⟨t, L, HB, c, hL, hc, hi, hinside, hbase, hproper,
    delta, hdelta, hdsmall, _, hopen⟩ :=
    he.exists_small_boundary_collar_of_interior_nonempty hR hne isOpen_univ (subset_univ _)
  let E := t → ℝ × V3
  let F := s → ℝ × V3
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T, hT, hTs, _⟩ := L.exists_finite_triangulation_prod J hL hJ
  rw [hJs] at hTs
  have hcphi : FinitePiecewiseAffineOn (phi ∘ c) (L.space ×ˢ I) := by
    have h := (hTs.symm ▸ hc).finitePiecewiseAffineOn_comp T hT hphiPL
    exact hTs ▸ h
  let a : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (delta • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hamap : MapsTo a (L.space ×ˢ I) (L.space ×ˢ I) := by
    intro z hz
    exact ⟨hz.1, mul_nonneg hdelta.le hz.2.1, by
      change delta * z.2 ≤ 1
      nlinarith [hz.2.2]⟩
  have haPL : FinitePiecewiseAffineOn a (L.space ×ˢ I) :=
    hTs ▸ (T.affineOnFaces_affine a).finitePiecewiseAffineOn hT
  let d : E × ℝ → F := (phi ∘ c) ∘ a
  have hdPL : FinitePiecewiseAffineOn d (L.space ×ˢ I) := hcphi.comp haPL hamap
  have hdval (z : E × ℝ) : d z = phi (c (z.1, delta * z.2)) := rfl
  have hdinj : InjOn d (L.space ×ˢ I) := by
    intro z hz w hw hzw
    have hcEq := hphii (hinside (hamap hz)) (hinside (hamap hw)) hzw
    have haEq := congrArg Subtype.val (hi.injective
      (a₁ := ⟨a z, hamap hz⟩) (a₂ := ⟨a w, hamap hw⟩) hcEq)
    have hfst := congrArg Prod.fst haEq
    have hsnd := congrArg Prod.snd haEq
    exact Prod.ext hfst (mul_left_cancel₀ hdelta.ne' hsnd)
  have hdinside : MapsTo d (L.space ×ˢ I) K.space := by
    intro z hz
    rw [hKs]
    exact mem_image_of_mem phi (hinside (hamap hz))
  let HB' : L.space ≃ₜ A.space := HB.trans HA.symm
  have hzero (z : L.space) : d ((z : E), 0) = HB' z := by
    rw [hdval, mul_zero, hbase]
    exact ((hHAinv (HB z)).trans (hH _)).symm
  have hdboundary (z : E × ℝ) (hz : z ∈ L.space ×ˢ I) :
      d z ∈ A.space ↔ z.2 = 0 := by
    change phi (c (a z)) ∈ A.space ↔ _
    rw [hmem _ (hinside (hamap hz))]
    have h := hproper ⟨a z, hamap hz⟩
    change c (a z) ∈ frontier R ↔ delta * z.2 = 0 at h
    exact h.trans (mul_eq_zero.trans (or_iff_right hdelta.ne'))
  have hopen_eq : d '' (L.space ×ˢ Ico (0 : ℝ) 1) =
      phi '' (c '' (L.space ×ˢ Ico (0 : ℝ) delta)) := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨c (a z), ⟨a z, ⟨hz.1, mul_nonneg hdelta.le hz.2.1, ?_⟩, rfl⟩, rfl⟩
      change delta * z.2 < delta
      nlinarith [hz.2.2]
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(z.1, z.2 / delta),
        ⟨hz.1, div_nonneg hz.2.1 hdelta.le, (div_lt_one hdelta).mpr hz.2.2⟩, ?_⟩
      rw [hdval]
      congr 2
      apply Prod.ext
      · rfl
      · dsimp
        field_simp
  have hstripR : c '' (L.space ×ˢ Ico (0 : ℝ) delta) ⊆ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact hinside ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  have hopenK : IsOpen ((Subtype.val : K.space → F) ⁻¹'
      (d '' (L.space ×ˢ Ico (0 : ℝ) 1))) := by
    have heq : (Subtype.val : K.space → F) ⁻¹'
        (d '' (L.space ×ˢ Ico (0 : ℝ) 1)) =
        H.symm ⁻¹' ((Subtype.val : R → X) ⁻¹'
          (c '' (L.space ×ˢ Ico (0 : ℝ) delta))) := by
      ext z
      rw [hopen_eq]
      change (z : F) ∈ phi '' (c '' (L.space ×ˢ Ico (0 : ℝ) delta)) ↔
        (H.symm z : X) ∈ c '' (L.space ×ˢ Ico (0 : ℝ) delta)
      constructor
      · rintro ⟨x, hx, hxz⟩
        have hh : H ⟨x, hstripR hx⟩ = z := Subtype.ext ((hH _).trans hxz)
        have hpoint : (H.symm z : X) = x := by rw [← hh, H.symm_apply_apply]
        exact hpoint.symm ▸ hx
      · intro hx
        exact ⟨H.symm z, hx, (hH _).symm.trans (congrArg Subtype.val (H.apply_symm_apply z))⟩
    rw [heq]
    exact (hopen delta hdelta le_rfl).preimage H.symm.continuous
  exact ⟨⟨s, phi, K, A, H, g, hphi, hphiPL, hK, hAK, hH, hg, hgPL,
    hboundary, t, L, HB', d, hL, hdPL, hdinj, hdinside, hzero, hdboundary, hopenK⟩⟩

end PoincareConjecture.M76
