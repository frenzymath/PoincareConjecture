import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Period.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Period.RoundBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Period.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientCylinderPeriod

variable {N U M : Type*}
  [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] [T3Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
  [SecondCountableTopology N] [CompactSpace N] [Nonempty N]
  [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U] [T3Space U]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) U] [IsManifold (𝓡 3) ∞ U]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem translation_eq_zero_of_round_ancient_cover
    (K : AncientKappaSolution 3 M) (F : RicciFlow 3 U (Iic 0))
    (H : RicciFlow 2 N (Iic 0))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (H.metric t) (H.connection t))
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ U)
    (he : ∀ t ≤ 0, ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (F.metric t).inner (e z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          (H.metric t).inner z.1 v.1 w.1 + v.2 * w.2)
    {p : U → M} (hp : ContMDiff (𝓡 3) (𝓡 3) ∞ p)
    (hsurj : Function.Surjective p)
    (hinner : ∀ t ≤ 0, ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      (F.metric t).inner x v w = (K.flow.metric t).inner (p x)
        (mfderiv (𝓡 3) (𝓡 3) p x v) (mfderiv (𝓡 3) (𝓡 3) p x w))
    (d : Equiv.Perm (N × ℝ)) (l : ℝ)
    (hd : ∀ z, (d z).2 = z.2 + l) (hdeck : ∀ z, p (e (d z)) = p (e z)) :
    l = 0 := by
  by_contra hl
  let x : N := Classical.choice inferInstance
  let a : ℝ := (H.connection 0).scalarCurvature x
  have ha : 0 < a := by
    obtain ⟨c, hc, heq⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
      (hround 0 le_rfl)
    change 0 < (H.connection 0).scalarCurvature x
    rwa [heq x]
  let V : ℝ≥0∞ := (H.metric 0).volumeMeasure univ
  have hV : V ≠ ⊤ :=
    (H.metric 0).volumeMeasure_lt_top_of_isCompact isCompact_univ |>.ne
  let C : ℝ := V.toReal * |l|
  refine K.not_linear_volume_growth_of_scalar_decay ?_ a C ha.le
    (mul_nonneg ENNReal.toReal_nonneg (abs_nonneg l)) ?_
  · intro t ht y
    obtain ⟨u, rfl⟩ := hsurj y
    obtain ⟨z, rfl⟩ := e.surjective u
    change (K.flow.connection t).scalarCurvature (p (e z)) ≤ (-t)⁻¹
    have hlocal := (F.connection t).scalarCurvature_eq_of_local_isometry
      (K.flow.connection t) isOpen_univ hp.contMDiffOn
      (fun u _ => hinner t ht.le u) (mem_univ (e z))
    rw [← hlocal, RiemannianMetric.scalarCurvature_eq_of_line_product
      (H.metric t) (F.metric t) (H.connection t) (F.connection t) e (he t ht.le)]
    exact H.scalarCurvature_le_inv_neg_time_of_round hround t ht z.1
  · intro t ht
    have hv := calibratedVolume_univ_le_of_translation
      (H.metric t) (F.metric t) (K.flow.metric t) e (he t ht)
      hp hsurj (hinner t ht) d l hl hd hdeck
    rw [H.volumeMeasure_eq_terminal_scale_of_round hround x t ht,
      Measure.smul_apply, smul_eq_mul] at hv
    have hs : 0 ≤ 1 - a * t := by nlinarith
    calc
      calibratedMetricVolume (K.flow.metric t) univ
          ≤ ENNReal.ofReal (1 - a * t) * V * ENNReal.ofReal |l| := hv
      _ = ENNReal.ofReal (C * (1 - a * t)) := by
        rw [← ENNReal.ofReal_toReal hV, ← ENNReal.ofReal_mul hs,
          ← ENNReal.ofReal_mul (mul_nonneg hs ENNReal.toReal_nonneg)]
        congr 1
        dsimp only [C]
        ring

end PoincareConjecture.AncientCylinderPeriod
