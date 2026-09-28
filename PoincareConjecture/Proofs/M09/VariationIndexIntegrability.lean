import PoincareConjecture.Proofs.M09.SmoothIndexDensity
import PoincareConjecture.Proofs.M09.CompactDerivativeExtension
import PoincareConjecture.Proofs.M09.VariationFieldSmooth








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T b τmax : ℝ}

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem secondVariationIndexDensity_intervalIntegrable
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hb : 0 < b) (hmax : b < τmax)
    {P : BackwardTimePath F T 0 b} (V : LVariation F T 0 b P)
    (D : LVariationDerivativeData V) :
    IntervalIntegrable (secondVariationIndexDensity V D) MeasureTheory.volume 0 (Real.sqrt b) := by
  let K := sqrtParameterInterval 0 b
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  obtain ⟨hU, hKU, _⟩ := squareVariationField_smooth V
  have hf : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z ↦ V.squareFamily z.1 z.2) V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hi : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s : ℝ ↦ (s, (0 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    hf.comp hi.contMDiffOn (fun _ hs ↦ hs)
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (le_refl 0) hb)
  have htime : K ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hs.1
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  obtain ⟨H⟩ := nonempty_pullbackDerivativeExtensionOn_compact F T τmax hτmax hwindow
    V.baseSquareCurve (squareVariationField V) U K hU hKU isCompact_Icc hKd htime hα
    D.variation_extension
  let g : ℝ → ℝ × M := fun s ↦ (s, V.baseSquareCurve s)
  have hg : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞ g U :=
    contMDiffOn_id.prodMk hα
  let W := U ∩ g ⁻¹' (D.velocity_extension.domain ∩ D.variation_extension.domain ∩ H.domain) ∩
    Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hW : IsOpen W := (hg.continuousOn.isOpen_inter_preimage hU
    ((D.velocity_extension.open_domain.inter D.variation_extension.open_domain).inter
      H.open_domain)).inter isOpen_Ioo
  have hKW : K ⊆ W := fun s hs ↦
    ⟨⟨hKU hs, ⟨D.velocity_extension.graph_mem s hs, D.variation_extension.graph_mem s hs⟩,
      H.graph_mem s hs⟩, htime hs⟩
  have hgW := hg.mono (show W ⊆ U from fun _ h ↦ h.1.1)
  let A := fun s ↦ D.velocity_extension.extension s (V.baseSquareCurve s)
  let Y := fun s ↦ D.variation_extension.extension s (V.baseSquareCurve s)
  let Z := fun s ↦ H.extension s (V.baseSquareCurve s)
  have hA : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨V.baseSquareCurve s, A s⟩ : TangentBundle (𝓡 n) M)) W :=
    D.velocity_extension.smooth.comp hgW (fun _ hs ↦ hs.1.2.1.1)
  have hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨V.baseSquareCurve s, Y s⟩ : TangentBundle (𝓡 n) M)) W :=
    D.variation_extension.smooth.comp hgW (fun _ hs ↦ hs.1.2.1.2)
  have hZ : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨V.baseSquareCurve s, Z s⟩ : TangentBundle (𝓡 n) M)) W :=
    H.smooth.comp hgW (fun _ hs ↦ hs.1.2.2)
  have hsmooth := pointwiseSecondVariationDensity_contDiffOn F hM04 T τmax hτmax hwindow
    V.baseSquareCurve A Y Z W hW Set.inter_subset_right
    (hα.mono (fun _ h ↦ h.1.1)) hA hY hZ
  have hcont : ContinuousOn (secondVariationIndexDensity V D) K := by
    apply (hsmooth.continuousOn.mono hKW).congr
    intro s hs
    rw [secondVariationIndexDensity_eq_pointwise]
    change _ = pointwiseSecondVariationDensity F T (V.baseSquareCurve s) s
      (D.velocity_extension.extension s (V.baseSquareCurve s))
      (D.variation_extension.extension s (V.baseSquareCurve s)) (H.extension s (V.baseSquareCurve s))
    rw [D.velocity_extension.agrees s hs, D.variation_extension.agrees s hs, H.agrees s hs]
  apply ContinuousOn.intervalIntegrable_of_Icc (Real.sqrt_nonneg b)
  simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hcont

end PoincareConjecture.Proofs.M09
