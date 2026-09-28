import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCutDeformationFamily
import PoincareConjecture.Proofs.M76.Mathlib.RelativePLSuperlevelFrontier












set_option autoImplicit false

open Set Geometry unitInterval

namespace OpenPartialHomeomorph









theorem exists_compact_PL_relative_deformation_neighborhood
    {M E G ι : Type*} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {C A R : Set M} (hC : IsCompact C) (hACint : A ⊆ interior C) (hAR : A ⊆ R)
    (K J : SimplicialComplex ℝ G) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (H : C ≃ₜ K.space) (F : M → G) (hF : Continuous F)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hHF : ∀ x : C, (H x : G) = F x) (hJA : J.space = F '' A)
    (ell : G →ᵃ[ℝ] ℝ) (halign : K.RespectsAffineHyperplane ell)
    (hR : IsClosed R)
    (hcut : ∀ x ∈ C, x ∈ R ↔ 0 ≤ ell (F x))
    (hzero : ∀ x ∈ C, x ∈ frontier R ↔ ell (F x) = 0)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ psi (B y)) :
    ∃ (z : M → ℝ) (t : ℝ), t ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) ∧
      Continuous z ∧ (∀ x ∈ A, z x = 1) ∧
      let P : Set M := {x | t ≤ z x}
      let N : Set M := {x | x ∈ R ∧ t ≤ z x}
      IsCompact P ∧ IsCompact N ∧ A ⊆ interior P ∧ A ⊆ N ∧ N ⊆ interior C ∧
        (∃ T : C(I × N, M), (∀ p, T p ∈ N) ∧
          (∀ x : N, T (0, x) = (x : M)) ∧
          (∀ x : N, T (1, x) ∈ A) ∧
          (∀ (tau : I) (x : N), (x : M) ∈ A → T (tau, x) = (x : M)) ∧
          ∀ (tau : I) (x : N), (x : M) ∈ frontier R → T (tau, x) ∈ frontier R) ∧
        (∀ x ∈ frontier N,
          ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
            psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
            (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y)) ∧
        ∀ x ∈ frontier R, z x = t →
          ∃ (psi eta : E →ᴬ[ℝ] ℝ) (u v : E) (B : OpenPartialHomeomorph M E),
            psi.contLinear u = 1 ∧ psi.contLinear v = 0 ∧ eta.contLinear v = 1 ∧
            x ∈ B.source ∧ psi (B x) = 0 ∧ eta (B x) = 0 ∧
            (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            (∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y)) ∧
            (∀ y ∈ B.source,
              (y ∈ frontier R ∧ t ≤ z y) ↔ (psi (B y) = 0 ∧ 0 ≤ eta (B y))) ∧
            ∀ y ∈ B.source,
              (z y = t ∧ y ∈ R) ↔ (psi (B y) = 0 ∧ eta (B y) ≤ 0) := by
  obtain ⟨z, Q, hQ, _, hz, hzoff, hzPL, hzA, hdeform⟩ :=
    exists_compact_PL_cut_deformation_family e hC hACint K J hK hJ
      H F hF hFPL hHF hJA ell halign
  obtain ⟨t, ht, hP, hN, hlevel, hcorners⟩ :=
    exists_compact_PL_relative_regular_level e hcompat hcover hz hzPL
      hQ hzoff hR hboundary
      (a := (1 / 3 : ℝ)) (b := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
  have ht0 : 0 < t := lt_trans (by norm_num) ht.1
  have ht1 : t < 1 := lt_trans ht.2 (by norm_num)
  obtain ⟨_, hAP, hPC, D, hDP, hD0, hD1, hDfix, hDpos, hDzero⟩ := hdeform t ht0 ht1
  let P : Set M := {x | t ≤ z x}
  let N : Set M := {x | x ∈ R ∧ t ≤ z x}
  have hNP : N ⊆ P := fun _ hx => hx.2
  have hNC : N ⊆ interior C := hNP.trans hPC
  let j : N → P := fun x => ⟨x, x.property.2⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let T : C(I × N, M) := ⟨fun p => D (p.1, j p.2),
    D.continuous.comp (continuous_fst.prodMk (hj.comp continuous_snd))⟩
  have hTC (tau : I) (x : N) : T (tau, x) ∈ C :=
    interior_subset (hPC (hDP (tau, j x)))
  have hxC (x : N) : (x : M) ∈ C := interior_subset (hNC x.property)
  have hTN (p : I × N) : T p ∈ N := by
    refine ⟨(hcut _ (hTC p.1 p.2)).mpr ?_, hDP (p.1, j p.2)⟩
    exact hDpos p.1 (j p.2) ((hcut _ (hxC p.2)).mp p.2.property.1)
  have hTzero (tau : I) (x : N) (hx : (x : M) ∈ frontier R) :
      T (tau, x) ∈ frontier R := by
    apply (hzero _ (hTC tau x)).mpr
    exact hDzero tau (j x) ((hzero _ (hxC x)).mp hx)
  have hcorner : ∀ x ∈ frontier R, z x = t →
      ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, (y ∈ R ∧ t ≤ z y) ↔ 0 ≤ psi (B y) := by
    intro x hx hxt
    obtain ⟨psi, eta, u, v, B, hpsi, _, _, hxB, hpsix, _, hBPL, hBR, _, _⟩ :=
      hcorners x hx hxt
    exact ⟨psi, u, B, hpsi, hxB, hpsix, hBPL, hBR⟩
  exact ⟨z, t, ht, hz, hzA, hP, hN, hAP,
    fun x hx => ⟨hAR hx, (show x ∈ P from interior_subset (hAP hx))⟩, hNC,
    ⟨T, hTN, fun x => hD0 (j x), fun x => hD1 (j x),
      fun tau x hx => hDfix tau (j x) hx, hTzero⟩,
    relative_superlevel_frontier_charts e hz hR hboundary hlevel hcorner, hcorners⟩

end OpenPartialHomeomorph
