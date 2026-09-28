import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Embedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

noncomputable def originalNestedCoefficients (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K)
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier) (j k : ℕ) :
    ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  fun z => ((S.rescaling ((S.nestedWindowLimit P j).geometric_limit.subsequence k)).flow.metric
    z.1).pullbackCoefficients (S.originalNestedSpatialMap P j k ∘ (extChartAt (𝓡 n) q).symm) z.2

theorem originalNestedCoefficients_eq (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K)
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier) (j k : ℕ)
    (t : ℝ) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q).target)
    (hs : S.initialWindowIdentification P j ((extChartAt (𝓡 n) q).symm y) ∈
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    S.originalNestedCoefficients P q j k (t, y) =
      S.nestedSpatialCoefficients P q j k (t + 1, y) := by
  let f := S.nestedSpatialMap P j k ∘ (extChartAt (𝓡 n) q).symm
  let e := (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm
  let R := S.rescaling ((S.nestedWindowLimit P j).geometric_limit.subsequence k)
  have hf : MDifferentiableAt (𝓡 n) (𝓡 n) f y :=
    ((S.nestedSpatialMap_contMDiffAt P j k hs).comp y
      ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy))).mdifferentiableAt (by simp)
  have hd := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (f y)) hf
  have hm : (S.smallBasedWindow j ((S.nestedWindowLimit P j).geometric_limit.subsequence k)).metricAt
      (t + 1) = R.flow.shrink.metric t := by
    change R.flow.shrink.metric (t + 1 + -1) = _
    congr 1
    ring
  change (R.flow.metric t).pullbackCoefficients (e ∘ f) y =
    ((S.smallBasedWindow j ((S.nestedWindowLimit P j).geometric_limit.subsequence k)).metricAt
      (t + 1)).pullbackCoefficients f y
  rw [hm]
  ext v w
  change (R.flow.metric t).inner (e (f y))
      (mfderiv (𝓡 n) (𝓡 n) (e ∘ f) y v) (mfderiv (𝓡 n) (𝓡 n) (e ∘ f) y w) =
    (R.flow.shrink.metric t).inner (f y)
      (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w)
  rw [hd]
  rfl

theorem tendstoUniformlyOn_originalNestedCoefficients_jets (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {σ : ℕ → ℕ}
    (hside : ∀ j, S.initialWindowIdentification P j ''
      closure ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion (σ j))
    (hjets : ∀ q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier, ∀ r : ℕ,
      ∀ A : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact A →
      A ⊆ Iio 1 ×ˢ (extChartAt (𝓡 n) q).target → TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ r (S.nestedSpatialCoefficients P q j (σ j)))
        (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.gluedShiftedAncientFlow P).metric z.1).pullbackCoefficients
            (extChartAt (𝓡 n) q).symm z.2)) atTop A)
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier) (r : ℕ)
    {A : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hAU : A ⊆ Iio 0 ×ˢ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun j => iteratedFDeriv ℝ r (S.originalNestedCoefficients P q j (σ j)))
      (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.ancientWindowLimit P).flow.metric z.1).pullbackCoefficients
          (extChartAt (𝓡 n) q).symm z.2)) atTop A := by
  let d : ℝ × EuclideanSpace ℝ (Fin n) := (1, 0)
  let shift := fun z : ℝ × EuclideanSpace ℝ (Fin n) => z + d
  have hshift : Continuous shift := continuous_id.add continuous_const
  have hshiftU : shift '' A ⊆ Iio 1 ×ˢ (extChartAt (𝓡 n) q).target := by
    rintro _ ⟨z, hz, rfl⟩
    have hh := hAU hz
    exact ⟨by change z.1 + 1 < 1; have := hh.1; change z.1 < 0 at this; linarith,
      by simpa only [shift, d, Prod.snd_add, add_zero] using hh.2⟩
  have h := ((hjets q r (shift '' A) (hA.image hshift) hshiftU).comp shift).mono
    (subset_preimage_image shift A)
  have hc : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (extChartAt (𝓡 n) q).symm z.2) A :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.comp continuous_snd.continuousOn
      (fun z hz => (hAU hz).2)
  obtain ⟨s, hs⟩ := (S.nestedWindowLimit P 0).geometric_limit.exists_exhaustion_superset
    (hA.image_of_continuousOn hc)
  apply (h.congr ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop s] with j hj z hz
    let V := (extChartAt (𝓡 n) q).target ∩ (extChartAt (𝓡 n) q).symm ⁻¹'
      (S.nestedWindowLimit P 0).geometric_limit.exhaustion j
    have hV : IsOpen V := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓡 n) q)
      ((S.nestedWindowLimit P 0).geometric_limit.exhaustion_open j)
    have heq : EqOn (S.originalNestedCoefficients P q j (σ j))
        (fun p => S.nestedSpatialCoefficients P q j (σ j) (p + d))
        ((univ : Set ℝ) ×ˢ V) := by
      intro p hp
      change S.originalNestedCoefficients P q j (σ j) (p.1, p.2) =
        S.nestedSpatialCoefficients P q j (σ j) (p.1 + 1, p.2 + 0)
      rw [add_zero]
      exact S.originalNestedCoefficients_eq P q j (σ j) p.1 hp.2.1
        (hside j (mem_image_of_mem _ (subset_closure hp.2.2)))
    have hzV : z ∈ (univ : Set ℝ) ×ˢ V :=
      ⟨mem_univ _, (hAU hz).2, (S.nestedWindowLimit P 0).geometric_limit.exhaustion_monotone hj
        (hs (mem_image_of_mem _ hz))⟩
    exact (iteratedFDeriv_comp_add_right (𝕜 := ℝ)
      (f := S.nestedSpatialCoefficients P q j (σ j)) r d z).symm.trans
        (((eqOn_iteratedFDeriv_of_isOpen (isOpen_univ.prod hV) heq r) hzV).symm)
  · intro z hz
    have heq : (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.gluedShiftedAncientFlow P).metric (p + d).1).pullbackCoefficients
          (extChartAt (𝓡 n) q).symm (p + d).2) =
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.ancientWindowLimit P).flow.metric p.1).pullbackCoefficients
            (extChartAt (𝓡 n) q).symm p.2) := by
      funext p
      change ((S.gluedShiftedAncientFlow P).metric (p.1 + 1)).pullbackCoefficients
        (extChartAt (𝓡 n) q).symm (p.2 + 0) = _
      rw [add_zero]
      rfl
    exact (iteratedFDeriv_comp_add_right (𝕜 := ℝ)
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.gluedShiftedAncientFlow P).metric p.1).pullbackCoefficients
          (extChartAt (𝓡 n) q).symm p.2) r d z).symm.trans
      (congrArg (fun f => iteratedFDeriv ℝ r f z) heq)

end PoincareConjecture.AncientRescalingSequence
