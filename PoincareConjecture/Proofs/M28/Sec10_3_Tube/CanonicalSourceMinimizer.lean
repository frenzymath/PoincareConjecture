import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RegionSourceMinimizers
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CanonicalOpenRegion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

theorem exists_canonical_source_minimizer_accuracy (P : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (H : ConnectedNeckCapCover g),
        H.epsilon ≤ epsilon₀ →
        ∀ (Q A : ℝ) (η : ℝ → M) (a b : ℝ), 0 < Q → a ≤ b →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b) → MapsTo η (Icc a b) H.X →
          g.pathELength η a b < ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) →
          D.scalarCurvature (η a) = 8 * Q →
          32 * (max H.cap_constant 2) ^ 4 * Q < D.scalarCurvature (η b) →
          ∃ U : Set M, IsOpen U ∧ H.X ⊆ U ∧ U ⊆ H.canonicalCarrierUnion ∧
            ∃ γ : ℝ → M,
              D.scalarCurvature (γ 0) ≤ 8 * max H.cap_constant 2 * Q ∧
              32 * (max H.cap_constant 2) ^ 3 * Q < D.scalarCurvature (γ 1) ∧
              D.scalarCurvature (η b) ≤ max H.cap_constant 2 * D.scalarCurvature (γ 1) ∧
              ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
              MapsTo γ (Icc (0 : ℝ) 1) U ∧
              g.pathELength γ 0 1 = intrinsicEDist g U (γ 0) (γ 1) ∧
              g.pathELength γ 0 1 ≠ ⊤ ∧
              g.pathELength γ 0 1 <
                ENNReal.ofReal ((A + 2 * endpointConnectorBudget H.epsilon H.cap_constant) *
                  Q ^ (-1 / 2 : ℝ)) := by
  obtain ⟨epsilonR, hRpos, hRthreshold, hregion⟩ := exists_region_source_minimizer_accuracy.{u}
  refine ⟨min epsilonR P.epsilon₀, lt_min hRpos P.epsilon₀_pos,
    (min_le_left _ _).trans hRthreshold, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D H hsmall Q A η a b hQ hab hη hηX hηL hz hy
  have hsmallR : H.epsilon ≤ epsilonR := hsmall.trans (min_le_left _ _)
  have hsmallP : H.epsilon ≤ P.epsilon₀ := hsmall.trans (min_le_right _ _)
  let V := H.canonicalOpenSet
  let DV := H.canonicalOpenConnection
  let HV := H.restrictToCanonicalUnion DV
  have hcap : HV.cap_constant = H.cap_constant :=
    H.restrictToCanonicalUnion_cap_constant DV
  let RV := H.canonicalOpenTopology P hsmallP
  obtain ⟨ηV, hηV, heq, hηlength⟩ := exists_intrinsicOpenMetric_path_lift g V hab hη
    (fun t ht => H.subset_canonicalCarrierUnion (hηX ht))
  have hηVX : MapsTo ηV (Icc a b) HV.X := by
    intro t ht
    change (ηV t : M) ∈ H.X
    change (Subtype.val ∘ ηV) t ∈ H.X
    rw [heq ht]
    exact hηX ht
  have hsource (t : ℝ) (ht : t ∈ Icc a b) :
      DV.scalarCurvature (ηV t) = D.scalarCurvature (η t) := by
    rw [intrinsicOpenMetric_scalarCurvature g V DV D]
    exact congrArg D.scalarCurvature (heq ht)
  have hzV : DV.scalarCurvature (ηV a) = 8 * Q :=
    (hsource a (left_mem_Icc.mpr hab)).trans hz
  have hyV : 32 * (max HV.cap_constant 2) ^ 4 * Q < DV.scalarCurvature (ηV b) := by
    rw [hsource b (right_mem_Icc.mpr hab)]
    exact hy
  obtain ⟨S, hSopen, hXS, γ, hlo, hhi, hcompare, hγ, hγS, hmin, hfinite, hbound⟩ :=
    hregion V (intrinsicOpenMetric g V) DV HV RV hsmallR Q A ηV a b hQ hab hηV hηVX
      (hηlength ▸ hηL) hzV hyV
  let U : Set M := (Subtype.val : V → M) '' S
  have hUopen : IsOpen U := V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap S hSopen
  have hUV : U ⊆ (V : Set M) := by
    rintro x ⟨v, _, rfl⟩
    exact v.property
  have hXU : H.X ⊆ U := by
    intro x hx
    let v : V := ⟨x, H.subset_canonicalCarrierUnion hx⟩
    exact ⟨v, hXS hx, rfl⟩
  have hpre : (Subtype.val : V → M) ⁻¹' U = S := preimage_image_eq S Subtype.val_injective
  have hlength := intrinsicOpenMetric_pathELength g V zero_le_one hγ
  have hscalar (t : ℝ) : DV.scalarCurvature (γ t) = D.scalarCurvature (γ t : M) :=
    intrinsicOpenMetric_scalarCurvature g V DV D (γ t)
  refine ⟨U, hUopen, hXU, hUV, Subtype.val ∘ γ, ?_, ?_, ?_,
    (contMDiff_subtype_val (I := 𝓡 3) (U := V)).comp_contMDiffOn hγ,
    fun t ht => ⟨γ t, hγS ht, rfl⟩, ?_, ?_, ?_⟩
  · simpa only [hscalar 0, hcap, Function.comp_apply] using hlo
  · simpa only [hscalar 1, hcap, Function.comp_apply] using hhi
  · simpa only [hsource b (right_mem_Icc.mpr hab), hscalar 1, hcap,
      Function.comp_apply] using hcompare
  · calc
      g.pathELength (Subtype.val ∘ γ) 0 1 =
          (intrinsicOpenMetric g V).pathELength γ 0 1 := hlength.symm
      _ = intrinsicEDist (intrinsicOpenMetric g V) S (γ 0) (γ 1) := hmin
      _ = intrinsicEDist g U (γ 0 : M) (γ 1 : M) := by
        rw [← hpre]
        exact intrinsicOpenMetric_intrinsicEDist g V hUV (γ 0) (γ 1)
  · rw [← hlength]
    exact hfinite
  · rw [← hlength]
    exact hbound

end PoincareConjecture.M28
