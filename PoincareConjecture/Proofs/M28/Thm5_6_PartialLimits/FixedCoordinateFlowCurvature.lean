import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FixedCoordinateFlowLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateCurvature
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ScalarConvergence
import PoincareConjecture.Proofs.M28.Mathlib.SpatialJetsWithin
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter PoincareConjecture.ChartDistance PoincareConjecture.SpacetimeBounds
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.FixedCoordinateFlowLimit

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {tau : ℝ} {F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0)}
  {V : Set (EuclideanSpace ℝ (Fin n))} {hV : IsOpen V} [Nonempty V]
  {e : ∀ k, V → M k}

omit [∀ k, IsManifold (𝓡 n) ∞ (M k)] in
private theorem parametrization_smooth
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k)) (k : ℕ) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (chartParametrization (fun _ : Unit => V) (fun _ => hV) (i := ()) (e k)) V := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  exact contMDiffOn_chartParametrization (fun _ : Unit => V) (fun _ => hV)
    (he k).contMDiff

omit [∀ k, IsManifold (𝓡 n) ∞ (M k)] in
private theorem parametrization_invertible
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (k : ℕ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ V) :
    (mfderiv (𝓡 n) (𝓡 n)
      (chartParametrization (fun _ : Unit => V) (fun _ => hV) (i := ()) (e k)) x).IsInvertible := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  have hd := mfderiv_chartParametrization (fun _ : Unit => V) (fun _ => hV)
    (i := ()) (⟨x, hx⟩ : V) ((he k).contMDiff ⟨x, hx⟩)
  rw [hd]
  exact ⟨(he k ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp), rfl⟩

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1800000 in



theorem spatial_twoJets (L : FixedCoordinateFlowLimit F V hV e) (htau : 0 < tau)
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (t : ℝ) (ht : t ∈ Icc (-tau) 0) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ V) :
    Tendsto (fun k => metricTwoJet
      (((F (L.subsequence k)).metric t).pullbackCoefficients
        (chartParametrization (fun _ : Unit => V) (fun _ => hV)
          (i := ()) (e (L.subsequence k)))) x) atTop
      (𝓝 (metricTwoJet (fun y => L.coefficients (t, y)) x)) := by
  have hJ : UniqueDiffOn ℝ (Icc (-tau) 0) := uniqueDiffOn_Icc (by linarith)
  have hs (k : ℕ) : ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => ((F k).metric z.1).pullbackCoefficients
        (chartParametrization (fun _ : Unit => V) (fun _ => hV) (i := ()) (e k)) z.2)
      (Icc (-tau) 0 ×ˢ V) :=
    (F k).smooth.contDiffOn_spacetime_pullbackCoefficients_within hV
      (parametrization_smooth he k)
  apply tendsto_metricTwoJet_of_uniform_bilinear_jets (K := {x}) _ (mem_singleton x)
  intro m _
  have hsub : {(t, x)} ⊆ Icc (-tau) 0 ×ˢ V := singleton_subset_iff.mpr ⟨ht, hx⟩
  have h := (L.jets m {(t, x)} isCompact_singleton hsub).iteratedFDeriv_spatial_slice
    hJ hV hsub (Eventually.of_forall fun k => hs (L.subsequence k))
    L.coefficients_smooth (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
  apply (h.comp (fun y => (t, y))).mono
  intro y hy
  rcases mem_singleton_iff.mp hy with rfl
  exact mem_singleton (t, y)



theorem coefficients_eq_canonical_germ (L : FixedCoordinateFlowLimit F V hV e)
    (t : ℝ) (ht : t ∈ Icc (-tau) 0) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ x : V, (L.flow.metric t).pullbackCoefficients (extChartAt (𝓡 n) x).symm =ᶠ[𝓝 x.val]
      (fun p => L.coefficients (t, p)) := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro x
  filter_upwards [hV.mem_nhds x.property] with p hp
  rw [RiemannianMetric.pullbackCoefficients_canonicalChart V hV
    (L.flow.metric t) x ⟨p, hp⟩]
  ext v w
  exact L.metric_coefficients t ht ⟨p, hp⟩ v w




theorem metric_inner_tendsto (L : FixedCoordinateFlowLimit F V hV e) (htau : 0 < tau)
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k)) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ t ∈ Icc (-tau) 0, ∀ (x : V) (v w : EuclideanSpace ℝ (Fin n)),
      Tendsto (fun k => ((F (L.subsequence k)).metric t).pullbackCoefficients
        (chartParametrization (fun _ : Unit => V) (fun _ => hV)
          (i := ()) (e (L.subsequence k))) x v w) atTop
        (𝓝 ((L.flow.metric t).inner x v w)) := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro t ht x v w
  have hcoeff : Tendsto (fun k => ((F (L.subsequence k)).metric t).pullbackCoefficients
      (chartParametrization (fun _ : Unit => V) (fun _ => hV)
        (i := ()) (e (L.subsequence k))) x.val) atTop
      (𝓝 (L.coefficients (t, x.val))) := by
    simpa only [metricTwoJet] using
      (L.spatial_twoJets htau he t ht x.property).fst_nhds
  rw [L.metric_coefficients t ht x v w]
  exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
    (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp hcoeff)

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in




theorem curvatureTensor_tendsto (L : FixedCoordinateFlowLimit F V hV e) (htau : 0 < tau)
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k)) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ t ∈ Icc (-tau) 0, ∀ (x : V) (v w y z : EuclideanSpace ℝ (Fin n)),
      let param := fun k => chartParametrization (fun _ : Unit => V) (fun _ => hV)
        (i := ()) (e (L.subsequence k))
      Tendsto (fun k => ((F (L.subsequence k)).connection t).curvatureTensor
        (param k x) (mfderiv (𝓡 n) (𝓡 n) (param k) x v)
        (mfderiv (𝓡 n) (𝓡 n) (param k) x w)
        (mfderiv (𝓡 n) (𝓡 n) (param k) x y)
        (mfderiv (𝓡 n) (𝓡 n) (param k) x z)) atTop
        (𝓝 ((L.flow.connection t).curvatureTensor x v w y z)) := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro t ht x v w y z
  let c := extChartAt (𝓡 n) x
  have hc : c.target = V := canonical_extChartAt_target
    (fun _ : Unit => V) (fun _ => hV) () x
  have hs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm V :=
    (contMDiffOn_extChartAt_symm x).mono (fun _ hp => hc.symm ▸ hp)
  have hi (p) (hp : p ∈ V) : (mfderiv (𝓡 n) (𝓡 n) c.symm p).IsInvertible := by
    have hp' : p ∈ c.target := hc.symm ▸ hp
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hp'
  have hnear : (L.flow.metric t).pullbackCoefficients c.symm =ᶠ[𝓝 x.val]
      (fun p => L.coefficients (t, p)) := L.coefficients_eq_canonical_germ t ht x
  have hj := L.spatial_twoJets htau he t ht x.property
  have hconv := tendsto_curvatureTensor_of_pullback_jets
    (fun k => (F (L.subsequence k)).connection t) (L.flow.connection t) hV x.property
    (fun k => parametrization_smooth he (L.subsequence k))
    (fun k _ hp => parametrization_invertible he (L.subsequence k) hp) hs hi
    (by simpa only [metricTwoJet, hnear.self_of_nhds] using hj.fst_nhds)
    (by simpa only [metricTwoJet, hnear.fderiv_eq] using hj.snd_nhds.fst_nhds)
    (by simpa only [metricTwoJet, hnear.fderiv.fderiv_eq]
      using hj.snd_nhds.snd_nhds) v w y z
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  change mfderiv (𝓡 n) (𝓡 n) c.symm (x.val) = ContinuousLinearMap.id ℝ _ at hd
  have hx : c.symm x.val = x := (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)
  have hvalue : (L.flow.connection t).curvatureTensor (c.symm x.val)
      (mfderiv (𝓡 n) (𝓡 n) c.symm x.val v) (mfderiv (𝓡 n) (𝓡 n) c.symm x.val w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm x.val y) (mfderiv (𝓡 n) (𝓡 n) c.symm x.val z) =
      (L.flow.connection t).curvatureTensor x v w y z := by
    rw [hd]
    change (L.flow.connection t).curvatureTensor (c.symm x.val) v w y z = _
    exact congrArg (fun p : V => (L.flow.connection t).curvatureTensor p
      (show EuclideanSpace ℝ (Fin n) from v) w y z) hx
  simpa only [hvalue] using hconv

end PoincareConjecture.M28.FixedCoordinateFlowLimit

namespace PoincareConjecture.M28.FixedCoordinateFlowLimit

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {tau : ℝ} {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}
  {V : Set (EuclideanSpace ℝ (Fin 3))} {hV : IsOpen V} [Nonempty V]
  {e : ∀ k, V → M k}

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in



theorem scalarCurvature_tendsto (L : FixedCoordinateFlowLimit F V hV e) (htau : 0 < tau)
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k)) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc (-tau) 0, ∀ x : V,
      Tendsto (fun k => ((F (L.subsequence k)).connection t).scalarCurvature
        (e (L.subsequence k) x)) atTop (𝓝 ((L.flow.connection t).scalarCurvature x)) := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro t ht x
  let c := extChartAt (𝓡 3) x
  have hc : c.target = V := canonical_extChartAt_target
    (fun _ : Unit => V) (fun _ => hV) () x
  have hx : x.val ∈ c.target := hc.symm ▸ x.property
  have hcx : c.symm x.val = x := (extChartAt (𝓡 3) x).left_inv (mem_extChartAt_source x)
  have hnear : (L.flow.metric t).pullbackCoefficients c.symm =ᶠ[𝓝 x.val]
      (fun p => L.coefficients (t, p)) := L.coefficients_eq_canonical_germ t ht x
  have hj := L.spatial_twoJets htau he t ht x.property
  have hj' : Tendsto (fun k => metricTwoJet
      (((F (L.subsequence k)).metric t).pullbackCoefficients
        (chartParametrization (fun _ : Unit => V) (fun _ => hV)
          (i := ()) (e (L.subsequence k)))) x.val) atTop
      (𝓝 (metricTwoJet ((L.flow.metric t).pullbackCoefficients c.symm) x.val)) := by
    simpa only [metricTwoJet, hnear.self_of_nhds, hnear.fderiv_eq,
      hnear.fderiv.fderiv_eq] using hj
  have hread := (tube.contDiffAt_jetScalarCurvature
    (J := metricTwoJet ((L.flow.metric t).pullbackCoefficients c.symm) x.val)
    ((L.flow.metric t).isInvertible_chartCoefficients x hx)).continuousAt.tendsto.comp hj'
  have hlimit : tube.jetScalarCurvature
      (metricTwoJet ((L.flow.metric t).pullbackCoefficients c.symm) x.val) =
      (L.flow.connection t).scalarCurvature x := by
    rw [tube.jetScalarCurvature_metricTwoJet_pullback (L.flow.connection t)
      (isOpen_extChartAt_target x) (contMDiffOn_extChartAt_symm x)
      (fun y hy => by
        simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
          isInvertible_mfderivWithin_extChartAt_symm hy) hx, hcx]
  rw [hlimit] at hread
  apply hread.congr'
  exact Eventually.of_forall fun k => by
    simpa only [chartParametrization_apply, Function.comp_apply] using
      tube.jetScalarCurvature_metricTwoJet_pullback ((F (L.subsequence k)).connection t)
        hV (parametrization_smooth he (L.subsequence k))
        (fun _ hy => parametrization_invertible he (L.subsequence k) hy) x.property

end PoincareConjecture.M28.FixedCoordinateFlowLimit
