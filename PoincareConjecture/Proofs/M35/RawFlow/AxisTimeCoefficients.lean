import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointRegularity
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicRadialVelocity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

variable {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)

private theorem raw_axis_pair_contDiffOn (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      (G.flow.metric p.1).inner (p.2 • e 2) (e i) (e i))
      (Ico 0 G.lifetime ×ˢ univ) := by
  have h := Heat.raw_metric_pair_family_contDiffOn G.flow (e i) (e i)
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1, p.2 • e 2)) :=
    contDiff_fst.prodMk (contDiff_snd.smul contDiff_const)
  exact h.comp hc.contDiffOn (fun _ hp => ⟨hp.1, mem_univ _⟩)

theorem raw_axisRadialCoefficient_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => axisRadialCoefficient (G.flow.metric p.1) p.2)
      (Ico 0 G.lifetime ×ˢ univ) := raw_axis_pair_contDiffOn G 2

theorem raw_axisAngularCoefficient_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => axisAngularCoefficient (G.flow.metric p.1) p.2)
      (Ico 0 G.lifetime ×ˢ univ) := raw_axis_pair_contDiffOn G 0

theorem raw_axisRadialSpeed_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => axisRadialSpeed (G.flow.metric p.1) p.2)
      (Ico 0 G.lifetime ×ˢ univ) :=
  (raw_axisRadialCoefficient_contDiffOn G).sqrt
    (fun p _ => (axisRadialCoefficient_pos (G.flow.metric p.1) p.2).ne')

theorem raw_axisWarpingRadius_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => axisWarpingRadius (G.flow.metric p.1) p.2)
      (Ico 0 G.lifetime ×ˢ univ) :=
  contDiffOn_snd.mul ((raw_axisAngularCoefficient_contDiffOn G).sqrt
    (fun p _ => (axisAngularCoefficient_pos (G.flow.metric p.1) p.2).ne'))

noncomputable def rawAxisSpeedTimeDerivative (t r : ℝ) : ℝ :=
  -(G.flow.connection t).ricci (r • e 2) (e 2) (e 2) /
    axisRadialSpeed (G.flow.metric t) r

theorem rawAxisSpeedTimeDerivative_contDiffOn :
    ContDiffOn ℝ ∞ (Function.uncurry (rawAxisSpeedTimeDerivative G))
      (Ico 0 G.lifetime ×ˢ univ) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1, p.2 • e 2)) :=
    contDiff_fst.prodMk (contDiff_snd.smul contDiff_const)
  have hm : MapsTo (fun p : ℝ × ℝ => (p.1, p.2 • e 2))
      (Ico 0 G.lifetime ×ˢ univ) (Ico 0 G.lifetime ×ˢ univ) :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hr := (Heat.raw_ricci_pair_family_contDiffOn G.flow (e 2) (e 2)).comp
    hc.contDiffOn hm
  exact hr.neg.div (raw_axisRadialSpeed_contDiffOn G)
    (fun p _ => (axisRadialSpeed_pos (G.flow.metric p.1) p.2).ne')

theorem raw_axisRadialSpeed_hasDerivWithinAt {t : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (r : ℝ) : HasDerivWithinAt (fun s => axisRadialSpeed (G.flow.metric s) r)
      (rawAxisSpeedTimeDerivative G t r) (Ico 0 G.lifetime) t := by
  have h := (G.flow.equation t ht (r • e 2) (e 2) (e 2)).sqrt
    (axisRadialCoefficient_pos (G.flow.metric t) r).ne'
  convert! h using 1
  change -(G.flow.connection t).ricci (r • e 2) (e 2) (e 2) /
    Real.sqrt (axisRadialCoefficient (G.flow.metric t) r) =
      -2 * (G.flow.connection t).ricci (r • e 2) (e 2) (e 2) /
        (2 * Real.sqrt (axisRadialCoefficient (G.flow.metric t) r))
  field_simp [(Real.sqrt_pos.mpr (axisRadialCoefficient_pos (G.flow.metric t) r)).ne']

theorem raw_axisWarpingRadius_hasDerivWithinAt {t : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (r : ℝ) : HasDerivWithinAt (fun s => axisWarpingRadius (G.flow.metric s) r)
      (-r * (G.flow.connection t).ricci (r • e 2) (e 0) (e 0) /
        Real.sqrt (axisAngularCoefficient (G.flow.metric t) r)) (Ico 0 G.lifetime) t := by
  have h := ((G.flow.equation t ht (r • e 2) (e 0) (e 0)).sqrt
    (axisAngularCoefficient_pos (G.flow.metric t) r).ne').const_mul r
  convert! h using 1
  change -r * (G.flow.connection t).ricci (r • e 2) (e 0) (e 0) /
      Real.sqrt (axisAngularCoefficient (G.flow.metric t) r) =
    r * (-2 * (G.flow.connection t).ricci (r • e 2) (e 0) (e 0) /
      (2 * Real.sqrt (axisAngularCoefficient (G.flow.metric t) r)))
  field_simp [(Real.sqrt_pos.mpr (axisAngularCoefficient_pos (G.flow.metric t) r)).ne']

end PoincareConjecture.M35.Uniqueness
