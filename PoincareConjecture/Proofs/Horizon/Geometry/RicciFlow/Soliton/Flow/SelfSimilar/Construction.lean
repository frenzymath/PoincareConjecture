import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.SelfSimilar.SmoothFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.SelfSimilar.Equation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryRicci
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SolitonFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (Φ : ℝ → M → M) (h0 : ∀ x, Φ 0 x = x)
  (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
  (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))

def timeMap (t : ℝ) : Diffeomorph (𝓡 n) (𝓡 n) M M ∞ where
  toFun := Φ t
  invFun := Φ (-t)
  left_inv x := by rw [← hadd, neg_add_cancel, h0]
  right_inv x := by rw [← hadd, add_neg_cancel, h0]
  contMDiff_toFun := hs.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := hs.comp (contMDiff_const.prodMk contMDiff_id)

variable (g : RiemannianMetric n M)

def metric (t : ℝ) : RiemannianMetric n M :=
  if ht : t < 0 then
    (rescaledMetric g (-t) (neg_pos.mpr ht)).pullbackOfLocalDiffeomorph
      (timeMap Φ h0 hadd hs (-Real.log (-t)))
      (timeMap Φ h0 hadd hs (-Real.log (-t))).isLocalDiffeomorph
  else g

theorem metric_inner {t : ℝ} (ht : t < 0) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    (metric Φ h0 hadd hs g t).inner x u v =
      (-t) * g.inner (Φ (-Real.log (-t)) x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x u)
        (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x v) := by
  rw [metric, dif_pos ht]
  rfl

theorem metric_minus_one : metric Φ h0 hadd hs g (-1) = g := by
  have he : (metric Φ h0 hadd hs g (-1)).inner = g.inner := by
    funext x
    ext u v
    rw [metric_inner Φ h0 hadd hs g (by norm_num)]
    have hzero : Φ 0 = id := funext h0
    rw [show -Real.log (-(-1 : ℝ)) = 0 by norm_num, hzero]
    simp
  generalize metric Φ h0 hadd hs g (-1) = g' at he ⊢
  cases g'
  cases g
  cases he
  rfl

theorem metric_smooth : RiemannianMetric.IsSmoothFamilyOn
    (metric Φ h0 hadd hs g) (Iio 0) := by
  rintro ⟨t, x⟩ ⟨ht, _⟩
  have hr : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun s : ℝ => -Real.log (-s)) t := by
    apply ContDiffAt.contMDiffAt
    exact ((contDiffAt_id.neg).log (neg_ne_zero.mpr (ne_of_lt ht))).neg
  have hF : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Φ (-Real.log (-p.1)) p.2) (t, x) :=
    (hs _).comp (t, x) ((hr.comp (t, x) contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := g.movingPullback_smul_contMDiffAt
    (F := fun t => Φ (-Real.log (-t))) hF
    (show ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => -p.1) (t, x) from contMDiffAt_fst.neg)
  apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have hneg : ∀ᶠ p : ℝ × M in 𝓝 (t, x), p.1 < 0 :=
    continuousAt_fst (Iio_mem_nhds ht)
  filter_upwards [hneg] with p hp
  congr 1
  ext u v
  exact metric_inner Φ h0 hadd hs g hp p.2 u v

theorem metric_ricci (D : LeviCivitaData g) {t : ℝ} (ht : t < 0) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    (metric Φ h0 hadd hs g t).leviCivitaData.ricci x u v =
      D.ricci (Φ (-Real.log (-t)) x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x u)
        (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x v) := by
  let e := timeMap Φ h0 hadd hs (-Real.log (-t))
  have he := (metric Φ h0 hadd hs g t).leviCivitaData.ricci_eq_of_local_isometry
    (rescaledMetric_connection g D (-t) (neg_pos.mpr ht)) isOpen_univ
    e.contMDiff.contMDiffOn
    (fun y _ a b => metric_inner Φ h0 hadd hs g ht y a b) (mem_univ x) u v
  rw [rescaledMetric_ricci] at he
  exact he

end PoincareConjecture.SolitonFlow

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

def flowOfCompleteGradientFlow (S : GradientShrinkingSolitonData n M)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ S.potential)
    (Φ : ℝ → M → M) (h0 : ∀ x, Φ 0 x = x)
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    (hΦ : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x)
      (S.connection.gradient S.potential)) : ShrinkingSolitonFlow S where
  flow :=
    { metric := SolitonFlow.metric Φ h0 hadd hs S.metric
      connection t := (SolitonFlow.metric Φ h0 hadd hs S.metric t).leviCivitaData
      interval := ordConnected_Iio
      nontrivial := ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩
      smooth := SolitonFlow.metric_smooth Φ h0 hadd hs S.metric
      equation := by
        intro t ht x u v
        rw [SolitonFlow.metric_ricci Φ h0 hadd hs S.metric S.connection ht]
        have hd := S.hasDerivAt_selfSimilar_inner hf hs hΦ x u v t ht
        apply (hd.congr_of_eventuallyEq ?_).hasDerivWithinAt
        filter_upwards [Iio_mem_nhds ht] with s hs'
        exact SolitonFlow.metric_inner Φ h0 hadd hs S.metric hs' x u v }
  at_minus_one := SolitonFlow.metric_minus_one Φ h0 hadd hs S.metric
  self_similar t ht := by
    refine ⟨⟨SolitonFlow.timeMap Φ h0 hadd hs (-Real.log (-t)), ?_⟩⟩
    intro x u v
    rw [abs_of_neg ht]
    exact SolitonFlow.metric_inner Φ h0 hadd hs S.metric ht x u v

end PoincareConjecture.GradientShrinkingSolitonData
