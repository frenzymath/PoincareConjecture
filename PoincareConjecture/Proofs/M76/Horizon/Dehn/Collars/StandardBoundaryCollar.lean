import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryDiskPush
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_standard_finite_boundary_collar
    {R : Set V3} (hR : IsCompact R) (hRne : R.Nonempty)
    (he : PLDomain (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) R) :
    ∃ (K : SimplicialComplex ℝ V3) (s : Finset R)
      (L : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : L.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → V3),
      K.faces.Finite ∧ K.space = R ∧ L.faces.Finite ∧
      FinitePiecewiseAffineOn c (L.space ×ˢ I) ∧ InjOn c (L.space ×ˢ I) ∧
      MapsTo c (L.space ×ˢ I) R ∧
      (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
      (∀ z ∈ L.space ×ˢ I, c z ∈ frontier R ↔ z.2 = 0) ∧
      IsOpen ((Subtype.val : R → V3) ⁻¹' (c '' (L.space ×ˢ Ico (0 : ℝ) 1))) := by
  let e := fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph
  have hid : ∀ j : Unit, LocallyPiecewiseAffineOn (id ∘ (e j).symm) (e j).target := by
    intro j
    exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) isOpen_univ
  obtain ⟨K, _, _, hK, _, _, hKs, _, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair e he.cover continuous_id hid
      hR (fun _ _ _ _ h ↦ h) he.halfspace
  simp only [image_id] at hKs
  have hne : (interior R).Nonempty := closure_nonempty_iff.mp
    (he.closure_interior.symm ▸ hRne)
  obtain ⟨D, _, hDR, ⟨b⟩⟩ := he.exists_ball_in_interior hne
  obtain ⟨s, L, HB, c, hL, hc, hi, hinside, hbase, hproper, δ, hδ, hδsmall, _, hopen⟩ :=
    exists_protected_small_boundary_collar hR he (hDR.trans interior_subset) b
      isOpen_univ (fun _ _ ↦ mem_univ _)
  let E := s → ℝ × V3
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨T, hT, hTs, _⟩ := L.exists_finite_triangulation_prod J hL hJ
  rw [hJs] at hTs
  have hcPL : FinitePiecewiseAffineOn c (L.space ×ˢ I) := by
    have h := (hTs.symm ▸ hc).finitePiecewiseAffineOn_fixed_chart he.compatible T hT ()
      (fun _ _ ↦ mem_univ _)
    exact hTs ▸ h
  let a : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (δ • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have haval (z : E × ℝ) : a z = (z.1, δ * z.2) := rfl
  have hamap : MapsTo a (L.space ×ˢ I) (L.space ×ˢ I) := by
    intro z hz
    exact ⟨hz.1, mul_nonneg hδ.le hz.2.1, by
      change δ * z.2 ≤ 1
      nlinarith [hz.2.2]⟩
  have haPL : FinitePiecewiseAffineOn a (L.space ×ˢ I) :=
    hTs ▸ (T.affineOnFaces_affine a).finitePiecewiseAffineOn hT
  let d : E × ℝ → V3 := c ∘ a
  have hdPL : FinitePiecewiseAffineOn d (L.space ×ˢ I) := hcPL.comp haPL hamap
  have hdval (z : E × ℝ) : d z = c (z.1, δ * z.2) := rfl
  have hdinj : InjOn d (L.space ×ˢ I) := by
    intro z hz w hw hzw
    have hsub := congrArg Subtype.val (hi.injective
      (a₁ := ⟨a z, hamap hz⟩) (a₂ := ⟨a w, hamap hw⟩) hzw)
    have hfst := congrArg Prod.fst hsub
    have hsnd := congrArg Prod.snd hsub
    apply Prod.ext
    · exact hfst
    · exact (mul_left_cancel₀ hδ.ne' hsnd)
  have hopen_eq : d '' (L.space ×ˢ Ico (0 : ℝ) 1) =
      c '' (L.space ×ˢ Ico (0 : ℝ) δ) := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨a z, ⟨hz.1, mul_nonneg hδ.le hz.2.1,
        by change δ * z.2 < δ; nlinarith [hz.2.2]⟩, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(z.1, z.2 / δ), ⟨hz.1, div_nonneg hz.2.1 hδ.le,
        (div_lt_one hδ).mpr hz.2.2⟩, ?_⟩
      rw [hdval]
      congr 1
      apply Prod.ext
      · rfl
      · dsimp
        field_simp
  refine ⟨K, s, L, HB, d, hK, hKs, hL, hdPL, hdinj,
    fun _ hz ↦ hinside (hamap hz), ?_, ?_, ?_⟩
  · intro x
    simpa only [hdval, mul_zero] using hbase x
  · intro z hz
    have h := hproper ⟨a z, hamap hz⟩
    change d z ∈ frontier R ↔ δ * z.2 = 0 at h
    exact h.trans (mul_eq_zero.trans (or_iff_right hδ.ne'))
  · rw [hopen_eq]
    exact hopen δ hδ le_rfl

end PoincareConjecture.M76.Dehn
