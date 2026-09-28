import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackRicciRegularity
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Definitions.M62Curve
import Mathlib.Topology.ContinuousMap.Compact










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)





theorem exists_closed_normalization_coefficient_limit
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (c : ℕ → ℝ → ℝ → M) (R S H : ℕ → C(Icc a b, X))
    (r s h : C(Icc a b, X))
    (hR : Tendsto R atTop (𝓝 r)) (hS : Tendsto S atTop (𝓝 s))
    (hH : Tendsto H atTop (𝓝 h))
    (hRrep : ∀ j (t : Icc a b) (x : ℝ),
      R j t (x : AddCircle curvePeriod) = e (c j x t))
    (hSrep : ∀ j (t : Icc a b) (x : ℝ), S j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (spatialUnitTangent F (c j) t x))
    (hHrep : ∀ j (t : Icc a b) (x : ℝ), H j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x))
    (hrU : ∀ (t : Icc a b) z, r t z ∈ U) :
    ∃ (A : ℕ → C(Icc a b, XR)) (A0 : C(Icc a b, XR)),
      Tendsto A atTop (𝓝 A0) ∧
      (∀ j (t : Icc a b) (x : ℝ), A j t (x : AddCircle curvePeriod) =
        m62TangentRicci F (c j) t x + m62CurvatureSquared F (c j) t x) ∧
      ∀ (t : Icc a b) z, A0 t z =
        (F.connection t).ricci (ρ (r t z))
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t z) (s t z))
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t z) (s t z)) +
        (F.metric t).inner (ρ (r t z))
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t z) (h t z))
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t z) (h t z)) := by
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  let Y := Icc a b × AddCircle curvePeriod
  let D := (Icc a b × U) × (W × W)
  have hRic := (flow_pullback_ricci_contDiffOn F hU hρ).continuousOn
  have hzero : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) :=
    contMDiff_const
  have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ hzero).1.continuousOn
  have hbase : Continuous (fun z : D => (z.1.1.1, z.1.2.1)) :=
    (continuous_subtype_val.comp continuous_fst.fst).prodMk
      (continuous_subtype_val.comp continuous_fst.snd)
  let N : C(D, ℝ) := ⟨fun z =>
    (F.connection z.1.1).ricci (ρ z.1.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1) +
    (F.metric z.1.1).inner (ρ z.1.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2),
    (hRic.comp_continuous (hbase.prodMk continuous_snd.fst)
      (fun z => ⟨⟨z.1.1.2, z.1.2.2⟩, mem_univ _⟩)).add
    (hmetric.comp_continuous (hbase.prodMk continuous_snd.snd)
      (fun z => ⟨⟨z.1.1.2, z.1.2.2⟩, mem_univ _⟩))⟩
  have hRU (j : ℕ) (y : Y) : (R j).uncurry y ∈ U := by
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective y.2
    change R j y.1 y.2 ∈ U
    rw [← hx, hRrep]
    exact heU (mem_range_self _)
  let Rn (j : ℕ) : C(Y, U) :=
    ⟨fun y => ⟨(R j).uncurry y, hRU j y⟩, (R j).uncurry.continuous.subtype_mk _⟩
  let r0 : C(Y, U) :=
    ⟨fun y => ⟨r.uncurry y, hrU y.1 y.2⟩, r.uncurry.continuous.subtype_mk _⟩
  let inc : C(U, W) := ⟨Subtype.val, continuous_subtype_val⟩
  have hRn : Tendsto Rn atTop (𝓝 r0) := by
    apply (inc.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    exact (ContinuousMap.continuous_uncurry.tendsto r).comp hR
  have hSn := (ContinuousMap.continuous_uncurry.tendsto s).comp hS
  have hHn := (ContinuousMap.continuous_uncurry.tendsto h).comp hH
  let T : C(Y, Icc a b) := ContinuousMap.fst
  let bundle (q : C(Y, U) × (C(Y, W) × C(Y, W))) : C(Y, D) :=
    (T.prodMk q.1).prodMk (q.2.1.prodMk q.2.2)
  have hbundle : Continuous bundle := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((T.continuous.comp continuous_snd).prodMk
      (continuous_fst.fst.eval continuous_snd)).prodMk
      ((continuous_fst.snd.fst.eval continuous_snd).prodMk
        (continuous_fst.snd.snd.eval continuous_snd))
  let An (j : ℕ) : C(Y, ℝ) :=
    N.comp (bundle (Rn j, (S j).uncurry, (H j).uncurry))
  let A0 : C(Y, ℝ) := N.comp (bundle (r0, s.uncurry, h.uncurry))
  have hAn : Tendsto An atTop (𝓝 A0) :=
    (N.continuous_postcomp.tendsto _).comp
      ((hbundle.tendsto _).comp (hRn.prodMk_nhds (hSn.prodMk_nhds hHn)))
  refine ⟨fun j => (An j).curry, A0.curry,
    (ContinuousMap.continuous_curry.tendsto A0).comp hAn, ?_, fun _ _ => rfl⟩
  intro j t x
  change (F.connection t).ricci (ρ (R j t (x : AddCircle curvePeriod)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R j t (x : AddCircle curvePeriod))
        (S j t (x : AddCircle curvePeriod)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R j t (x : AddCircle curvePeriod))
        (S j t (x : AddCircle curvePeriod))) +
    (F.metric t).inner (ρ (R j t (x : AddCircle curvePeriod)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R j t (x : AddCircle curvePeriod))
        (H j t (x : AddCircle curvePeriod)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R j t (x : AddCircle curvePeriod))
        (H j t (x : AddCircle curvePeriod))) = _
  rw [hRrep, hSrep, hHrep]
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  rw [hleft, hleft, hρe]
  rfl

end PoincareConjecture.M63
