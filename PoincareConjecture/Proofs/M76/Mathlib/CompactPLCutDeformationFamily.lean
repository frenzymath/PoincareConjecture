import PoincareConjecture.Proofs.M76.Mathlib.FullSubcomplexConfinement
import PoincareConjecture.Proofs.M76.Mathlib.FullSubcomplexAffineCutDeformation
import PoincareConjecture.Proofs.M76.Mathlib.SupportedPolyhedralPLPullback

set_option autoImplicit false

open Set Geometry unitInterval

namespace OpenPartialHomeomorph

theorem exists_compact_PL_cut_deformation_family_mass
    {M E G ι : Type*} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (e : ι → OpenPartialHomeomorph M E)
    {C A : Set M} (hC : IsCompact C) (hACint : A ⊆ interior C)
    (K J : SimplicialComplex ℝ G) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (H : C ≃ₜ K.space) (F : M → G) (hF : Continuous F)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hHF : ∀ x : C, (H x : G) = F x) (hJA : J.space = F '' A)
    (ell : G →ᵃ[ℝ] ℝ) (halign : K.RespectsAffineHyperplane ell) :
    ∃ (z : M → ℝ) (Q : Set M), IsCompact Q ∧ Q ⊆ interior C ∧
      Continuous z ∧ (∀ x, x ∉ Q → z x = 0) ∧
      (∀ i, LocallyPiecewiseAffineOn (z ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ A, z x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let N : Set M := {x | c ≤ z x}
        IsCompact N ∧ A ⊆ interior N ∧ N ⊆ interior C ∧
          ∃ T : C(I × N, M), (∀ p, T p ∈ N) ∧
            (∀ x : N, T (0, x) = (x : M)) ∧
            (∀ x : N, T (1, x) ∈ A) ∧
            (∀ (t : I) (x : N), (x : M) ∈ A → T (t, x) = (x : M)) ∧
            (∀ (t : I) (x : N), 0 ≤ ell (F x) → 0 ≤ ell (F (T (t, x)))) ∧
            (∀ (t : I) (x : N), ell (F x) = 0 → ell (F (T (t, x))) = 0) ∧
            ∀ (t : I) (x : N), z (T (t, x)) =
              (1 - (t : ℝ)) * z x + (t : ℝ) := by
  classical
  have hAC : A ⊆ C := hACint.trans interior_subset
  have hFK : MapsTo F C K.space := by
    intro x hx
    rw [← hHF ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hFinj : InjOn F C := by
    intro x hx y hy hxy
    have he : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective he)
  have hFH (y : K.space) : F (H.symm y) = (y : G) :=
    (hHF (H.symm y)).symm.trans (congrArg Subtype.val (H.apply_symm_apply y))
  have hJpre (x : M) (hx : x ∈ C) : F x ∈ J.space ↔ x ∈ A := by
    constructor
    · intro hxJ
      rw [hJA] at hxJ
      obtain ⟨a, ha, hax⟩ := hxJ
      exact hFinj (hAC ha) hx hax ▸ ha
    · intro hxA
      rw [hJA]
      exact mem_image_of_mem F hxA
  have hJK : J.space ⊆ K.space := by
    intro y hy
    rw [hJA] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hFK (hAC hx)
  let O : Set K.space := {y | (H.symm y : M) ∈ interior C}
  have hO : IsOpen O := isOpen_interior.preimage
    (continuous_subtype_val.comp H.symm.continuous)
  have hJO (y : K.space) (hy : (y : G) ∈ J.space) : y ∈ O := by
    apply hACint
    apply (hJpre _ (H.symm y).property).mp
    rwa [hFH]
  obtain ⟨R, L, P, hR, hRK, hLR, hLJ, hfull, hP, _, hPO, hfaces⟩ :=
    K.exists_full_subcomplex_confined_neighborhood J hK hJ hJK hO hJO
  obtain ⟨w, hw, hwv, hwL, hdeform⟩ :=
    R.exists_full_subcomplex_affine_cut_deformation_mass L hR hLR hfull ell
      (hRK.respectsAffineHyperplane halign)
  have hwzero (y : G) (hy : y ∈ R.space) (hyP : y ∉ P) : w y = 0 := by
    obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp hy
    have hvnot (v : G) (hv : v ∈ s) : v ∉ L.vertices := by
      intro hvL
      have hvJ : v ∈ J.space := hLJ ▸ L.vertices_subset_space hvL
      exact hyP (hfaces s hs ⟨v, subset_convexHull ℝ _ hv, hvJ⟩ hys)
    have hvalues : w '' (s : Set G) ⊆ ({0} : Set ℝ) := by
      rintro _ ⟨v, hv, rfl⟩
      change w v = 0
      have hvR : v ∈ R.vertices := R.down_closed hs
        (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      rw [hwv v hvR, if_neg (hvnot v hv)]
    simpa using hw.mapsTo_convexHull hs hvalues hys
  have hFR : MapsTo F C R.space := fun x hx => hRK.space_eq.symm ▸ hFK hx
  have hPinside (x : M) (hx : x ∈ C) (hxP : F x ∈ P) : x ∈ interior C := by
    obtain ⟨y, hyO, hyF⟩ := hPO hxP
    have he : (H.symm y : M) = x :=
      hFinj (H.symm y).property hx ((hFH y).trans hyF)
    have hyint : (H.symm y : M) ∈ interior C := hyO
    exact he ▸ hyint
  obtain ⟨z, Q, hQ, hQC, hz, hzC, hzoff, hzPL⟩ :=
    exists_compactly_supported_PL_pullback e hF hFPL R hC hFR
      (hw.finitePiecewiseAffineOn hR) hP.isClosed hwzero hPinside
  have hzA (x : M) (hx : x ∈ A) : z x = 1 :=
    (hzC (hAC hx)).trans (hwL _ (hLJ.symm ▸ (hJpre x (hAC hx)).mpr hx))
  refine ⟨z, Q, hQ, hQC, hz, hzoff, hzPL, hzA, ?_⟩
  intro c hc hc1
  let N : Set M := {x | c ≤ z x}
  have hNQ : N ⊆ Q := by
    intro x hx
    by_contra hxQ
    have hcx : c ≤ z x := hx
    rw [hzoff x hxQ] at hcx
    exact (not_le_of_gt hc) hcx
  have hN : IsCompact N := hQ.of_isClosed_subset (isClosed_le continuous_const hz) hNQ
  have hNC : N ⊆ interior C := hNQ.trans hQC
  have hAN : A ⊆ interior N := by
    intro x hx
    apply interior_maximal (show {y | c < z y} ⊆ N from
      fun y hy => (show c < z y from hy).le) (isOpen_lt continuous_const hz)
    change c < z x
    rw [hzA x hx]
    exact hc1
  let S : Set G := {y | y ∈ R.space ∧ c ≤ w y}
  obtain ⟨D, hDS, hD0, hD1, hDfix, hDpos, hDzero, hDmass⟩ := hdeform c hc hc1
  have hxC (x : N) : (x : M) ∈ C := interior_subset (hNC x.property)
  let j : N → S := fun x => ⟨F x, hFR (hxC x), by
    have hzx : z x = w (F x) := hzC (hxC x)
    rw [← hzx]
    exact x.property⟩
  have hj : Continuous j := (hF.comp continuous_subtype_val).subtype_mk _
  let inv : S → M := fun y => H.symm ⟨y, hRK.space_eq ▸ y.property.1⟩
  have hinvC (y : S) : inv y ∈ C := (H.symm ⟨y, hRK.space_eq ▸ y.property.1⟩).property
  have hFinv (y : S) : F (inv y) = (y : G) := hFH ⟨y, hRK.space_eq ▸ y.property.1⟩
  have hinvc : Continuous inv := continuous_subtype_val.comp
    (H.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hinvN (y : S) : inv y ∈ N := by
    change c ≤ z (inv y)
    rw [hzC (hinvC y)]
    change c ≤ w (F (inv y))
    rw [hFinv]
    exact y.property.2
  have hinvj (x : N) : inv (j x) = x := hFinj (hinvC (j x)) (hxC x) (hFinv (j x))
  have hinvA (y : S) (hy : (y : G) ∈ L.space) : inv y ∈ A := by
    apply (hJpre _ (hinvC y)).mp
    rw [hFinv]
    exact hLJ ▸ hy
  let d : I × N → S := fun p => ⟨D (p.1, j p.2), hDS (p.1, j p.2)⟩
  have hd : Continuous d := (D.continuous.comp
    (continuous_fst.prodMk (hj.comp continuous_snd))).subtype_mk _
  let T : C(I × N, M) := ⟨inv ∘ d, hinvc.comp hd⟩
  have hT0 (x : N) : T (0, x) = (x : M) := by
    have he : d (0, x) = j x := Subtype.ext (hD0 (j x))
    change inv (d (0, x)) = x
    rw [he]
    exact hinvj x
  have hTfix (t : I) (x : N) (hx : (x : M) ∈ A) : T (t, x) = (x : M) := by
    have hFxL : F x ∈ L.space := hLJ.symm ▸ (hJpre x (hxC x)).mpr hx
    have he : d (t, x) = j x := Subtype.ext (hDfix t (j x) hFxL)
    change inv (d (t, x)) = x
    rw [he]
    exact hinvj x
  refine ⟨hN, hAN, hNC, T, fun p => hinvN (d p), hT0,
    fun x => hinvA (d (1, x)) (hD1 (j x)), hTfix, ?_, ?_, ?_⟩
  · intro t x hx
    change 0 ≤ ell (F (inv (d (t, x))))
    rw [hFinv]
    exact hDpos t (j x) hx
  · intro t x hx
    change ell (F (inv (d (t, x)))) = 0
    rw [hFinv]
    exact hDzero t (j x) hx
  · intro t x
    change z (inv (d (t, x))) = (1 - (t : ℝ)) * z x + (t : ℝ)
    rw [hzC (hinvC (d (t, x))), Function.comp_apply, hFinv]
    change w (D (t, j x)) = (1 - (t : ℝ)) * z x + (t : ℝ)
    rw [hDmass]
    change (1 - (t : ℝ)) * w (F x) + (t : ℝ) = _
    exact congrArg (fun a => (1 - (t : ℝ)) * a + (t : ℝ)) (hzC (hxC x)).symm

theorem exists_compact_PL_cut_deformation_family
    {M E G ι : Type*} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (e : ι → OpenPartialHomeomorph M E)
    {C A : Set M} (hC : IsCompact C) (hACint : A ⊆ interior C)
    (K J : SimplicialComplex ℝ G) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (H : C ≃ₜ K.space) (F : M → G) (hF : Continuous F)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hHF : ∀ x : C, (H x : G) = F x) (hJA : J.space = F '' A)
    (ell : G →ᵃ[ℝ] ℝ) (halign : K.RespectsAffineHyperplane ell) :
    ∃ (z : M → ℝ) (Q : Set M), IsCompact Q ∧ Q ⊆ interior C ∧
      Continuous z ∧ (∀ x, x ∉ Q → z x = 0) ∧
      (∀ i, LocallyPiecewiseAffineOn (z ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ A, z x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let N : Set M := {x | c ≤ z x}
        IsCompact N ∧ A ⊆ interior N ∧ N ⊆ interior C ∧
          ∃ T : C(I × N, M), (∀ p, T p ∈ N) ∧
            (∀ x : N, T (0, x) = (x : M)) ∧
            (∀ x : N, T (1, x) ∈ A) ∧
            (∀ (t : I) (x : N), (x : M) ∈ A → T (t, x) = (x : M)) ∧
            (∀ (t : I) (x : N), 0 ≤ ell (F x) → 0 ≤ ell (F (T (t, x)))) ∧
            ∀ (t : I) (x : N), ell (F x) = 0 → ell (F (T (t, x))) = 0 := by
  obtain ⟨z, Q, hQ, hQC, hz, hzoff, hzPL, hzA, hlevel⟩ :=
    exists_compact_PL_cut_deformation_family_mass e hC hACint K J hK hJ H F hF
      hFPL hHF hJA ell halign
  refine ⟨z, Q, hQ, hQC, hz, hzoff, hzPL, hzA, ?_⟩
  intro c hc hc1
  obtain ⟨hN, hAN, hNC, T, hTN, hT0, hT1, hfix, hpos, hzero, _⟩ := hlevel c hc hc1
  exact ⟨hN, hAN, hNC, T, hTN, hT0, hT1, hfix, hpos, hzero⟩

end OpenPartialHomeomorph
