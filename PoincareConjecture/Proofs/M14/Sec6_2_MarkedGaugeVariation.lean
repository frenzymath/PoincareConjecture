import PoincareConjecture.Proofs.M14.Sec6_2_ClosedGaugeVariation
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedGaugeField









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}




theorem exists_markedGauge_variation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (R : M14SquareRootPath G p) (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b) (hsU : R.curve s ∈ U)
    {J : Set ℝ} (hJ : IsOpen J) (hsJ : s ∈ J) (w : EuclideanSpace ℝ (Fin n)) :
    ∃ V : M14LVariationData G p R,
      (∀ r ∈ M14SqrtParameterInterval a b, r ∉ J → ∀ v, V.squareFamily r v = R.curve r) ∧
      (∀ v, V.squareFamily s v = (G.gaugeCover.cylinder j).toSpacetime
        ((lift (R.curve s)).1,
          (G.gaugeCover.spatial j).affineShift (lift (R.curve s)).2 (v • w))) ∧
      (M14VariationField V s).val = ((G.gaugeCover.metric j).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 w).val := by
  have hpre : R.curve ⁻¹' U ∈ 𝓝[M14SqrtParameterInterval a b] s :=
    (R.smooth.continuousOn.mono R.interval_subset s hs).preimage_mem_nhdsWithin
      (hU.mem_nhds hsU)
  obtain ⟨K, hK, hsK, hKsub⟩ := mem_nhdsWithin.mp hpre
  obtain ⟨ζ, hζsupport, _, hζ, _, hζone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) ((hK.inter hJ).mem_nhds ⟨hsK, hsJ⟩)
  let η := fun r => ζ r • w
  have hη : ContDiff ℝ ∞ η := hζ.smul contDiff_const
  have hηsupport : tsupport η ⊆ K ∩ J :=
    (tsupport_smul_subset_left ζ (fun _ => w)).trans hζsupport
  have hsrc : ∀ r ∈ M14SqrtParameterInterval a b ∩ tsupport η, R.curve r ∈ U :=
    fun _ hr => hKsub ⟨(hηsupport hr.2).1, hr.1⟩
  obtain ⟨V, hV⟩ := exists_supportedGauge_variation_closed R j lift η hM12 hU hlift
    hright hη hsrc
  refine ⟨V, ?_, ?_, ?_⟩
  · intro r hr hnot v
    rw [hV r hr v]
    exact supportedGaugeFamily_eq_of_not_tsupport R j lift η
      (fun ht => hnot (hηsupport ht).2)
  · intro v
    rw [hV s hs v, supportedGaugeFamily_eq_gauge R j lift η (hright _ hsU)]
    simp only [gaugeShiftFamily, η, hζone, one_smul]
  · simpa only [η, hζone, one_smul] using
      variationField_supportedGauge_val_at R j lift η V hs (hV s hs) (hright _ hsU)

end PoincareConjecture.M14
