import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Localized
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_supported_germ_of_stationary
    {D : E -> E} (hD : ContDiff Real ∞ D)
    {P K C U : Set E} (hP : IsCompact P) (hK : IsCompact K) (hKP : K ⊆ P)
    (hfix : ∀ x ∈ P, D x = x)
    (hder : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ P,
      Function.Bijective (fderiv Real (fun y => (1 - t) • y + t • D y) x))
    (hU : IsOpen U) (hKU : K ⊆ U) (hUC : U ∩ C ⊆ P) :
    ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧
      ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
        ∃ F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
          (∀ x ∉ S, F x = x) ∧ EqOn F D V ∧ ∀ x ∈ C, F x = x := by
  let H : Real × E -> E := fun z => (1 - z.1) • z.2 + z.1 • D z.2
  have hH : ContDiff Real ∞ H :=
    ((contDiff_const.sub contDiff_fst).smul contDiff_snd).add
      (contDiff_fst.smul (hD.comp contDiff_snd))
  have hPz (t : Real) (x : E) (hx : x ∈ P) : H (t, x) = x := by
    simp only [H, hfix x hx, ← add_smul, sub_add_cancel, one_smul]
  obtain ⟨e, he, heq, _, hei⟩ :=
    exists_spacetime_neighborhood_of_codimZero_isotopy (a := 0) (b := 1) hP H hH
      (by intro t _ x hx y hy hxy; simpa only [hPz t x hx, hPz t y hy] using hxy)
      hder
  have hopen : IsOpen (e.source ∩ H ⁻¹' U) :=
    e.open_source.inter (hU.preimage hH.continuous)
  have htrace : Icc (0 : Real) 1 ×ˢ K ⊆ e.source ∩ H ⁻¹' U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨he ⟨ht, hKP hx⟩, ?_⟩
    change H (t, x) ∈ U
    rw [hPz t x (hKP hx)]
    exact hKU hx
  obtain ⟨T₀, V₀, _, hV₀, hIT₀, hKV₀, hTV⟩ :=
    generalized_tube_lemma isCompact_Icc hK hopen htrace
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV₀ hKV₀
  let K₁ : Set E := cthickening δ K
  have hK₁ : IsCompact K₁ := hK.cthickening
  have hK₁e : Icc (0 : Real) 1 ×ˢ K₁ ⊆ e.source := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact (hTV ⟨hIT₀ ht, hδV hx⟩).1
  have htraceK₁ (t : Real) (ht : t ∈ Icc (0 : Real) 1) (x : E) (hx : x ∈ K₁) :
      H (t, x) ∈ U := (hTV ⟨hIT₀ ht, hδV hx⟩).2
  have hKe : Icc (0 : Real) 1 ×ˢ (K₁ ∪ P) ⊆ e.source := by
    rintro ⟨t, x⟩ ⟨ht, hx | hx⟩
    · exact hK₁e ⟨ht, hx⟩
    · exact he ⟨ht, hx⟩
  obtain ⟨W, hW, hWc, hWon⟩ := exists_velocity_extension_of_compact_isotopy
    (hK₁.union hP) H hH e hKe hei (fun t ht x hx => heq (hKe ⟨ht, hx⟩))
  let T := H '' (Icc (0 : Real) 1 ×ˢ K₁)
  have hT : IsCompact T := (isCompact_Icc.prod hK₁).image hH.continuous
  have hTU : T ⊆ U := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact htraceK₁ t ht x hx
  obtain ⟨S, hS, hTS, hSU⟩ := exists_compact_between hT hU hTU
  obtain ⟨chi, hchi, hchi0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, E)
      hT.isClosed hTS (n := ⊤)
  let Z : Real × E -> E := fun p => chi p.2 • W p
  have hZ : ContDiff Real ∞ Z := (chi.contMDiff.contDiff.comp contDiff_snd).smul hW
  have hZc : HasCompactSupport Z := by
    exact HasCompactSupport.smul_left (R := Real) (M := E)
      (f := fun p : Real × E => chi p.2) hWc
  have hzero (t : Real) (x : E) (hx : x ∉ S) : Z (t, x) = 0 := by
    simp only [Z, hchi0 x hx, zero_smul]
  have hZon (t : Real) (ht : t ∈ Icc (0 : Real) 1) (x : E) (hx : x ∈ K₁) :
      Z (t, H (t, x)) = fderiv Real H (t, x) (1, 0) := by
    have hp : H (t, x) ∈ T := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    change chi (H (t, x)) • W (t, H (t, x)) = _
    rw [hchi.self_of_nhdsSet _ hp, one_smul, hWon t ht x (Or.inl hx)]
  have hpath (s : Real) (x : E) : HasDerivAt (fun r => H (r, x))
      (fderiv Real H (s, x) (1, 0)) s :=
    (hH.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hZprotected (t : Real) (ht : t ∈ Icc (0 : Real) 1) (x : E) (hxC : x ∈ C) :
      Z (t, x) = 0 := by
    by_cases hx : x ∈ S
    · have hxP : x ∈ P := hUC ⟨hSU hx, hxC⟩
      have hd := hpath t x
      have hconst : (fun r => H (r, x)) = fun _ : Real => x :=
        funext (fun r => hPz r x hxP)
      rw [hconst] at hd
      have hd0 := hd.unique (hasDerivAt_const t x)
      have hw := hWon t ht x (Or.inr hxP)
      rw [hPz t x hxP, hd0] at hw
      simp only [Z, hw, smul_zero]
    · exact hzero t x hx
  obtain ⟨Phi, hi, _, ho, hfixPhi⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support Z hZ hS hzero
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hZc hZ (by simp)
  have hLip (s : Real) : LipschitzWith L (fun y => Z (s, y)) := by
    convert! hL.comp (LipschitzWith.prodMk_left s) using 1
    simp
  have hagree (x : E) (hx : x ∈ K₁) : Phi 0 1 x = D x := by
    have heq := ODE_solution_unique hLip
      (HasDerivAt.continuousOn (fun s _ => ho 0 (H (0, x)) s))
      (fun s _ => (ho 0 (H (0, x)) s).hasDerivWithinAt)
      (hH.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun s hs => by
        change HasDerivWithinAt (fun r => H (r, x)) (Z (s, H (s, x))) (Ici s) s
        rw [hZon s (Ico_subset_Icc_self hs) x hx]
        exact (hpath s x).hasDerivWithinAt)
      (hi 0 (H (0, x)))
    simpa only [Function.comp_apply, id_eq, H, sub_zero, one_smul, zero_smul,
      add_zero, sub_self, zero_add]
      using heq (show (1 : Real) ∈ Icc 0 1 from ⟨by norm_num, le_rfl⟩)
  refine ⟨S, hS, hSU, thickening δ K, isOpen_thickening,
    self_subset_thickening hδ K, Phi 0 1, hfixPhi 0 1, ?_, ?_⟩
  · intro x hx
    exact hagree x (thickening_subset_cthickening δ K hx)
  · intro x hxC
    have heq := ODE_solution_unique hLip
      (HasDerivAt.continuousOn (fun s _ => ho 0 x s))
      (fun s _ => (ho 0 x s).hasDerivWithinAt)
      continuous_const.continuousOn
      (fun s hs => by
        change HasDerivWithinAt (fun _ : Real => x) (Z (s, x)) (Ici s) s
        rw [hZprotected s (Ico_subset_Icc_self hs) x hxC]
        exact (hasDerivAt_const s x).hasDerivWithinAt)
      (hi 0 x)
    exact heq ⟨by norm_num, le_rfl⟩

end Poincare.Manifold.Schoenflies.Reverse
