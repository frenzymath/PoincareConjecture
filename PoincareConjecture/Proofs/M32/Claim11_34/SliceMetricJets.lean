import PoincareConjecture.Proofs.M32.Claim11_34.SpatialJets
import PoincareConjecture.Proofs.M32.Claim11_34.Noncompact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private theorem slice_pullbackCoefficient_eq
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (-G.exhaustion.time k) 0)
    (q : G.limit.carrier.carrier) (y : EuclideanSpace ℝ (Fin 3))
    (hy : y ∈ (extChartAt (𝓡 3) q).target)
    (hspace : (extChartAt (𝓡 3) q).symm y ∈ G.exhaustion.space k)
    (a b : Fin 3) :
    (rescaledMetric ((S.flow (G.subsequence k)).metric
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
      (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))).pullbackCoefficients
        ((G.embedding k).forward t ht ∘ (extChartAt (𝓡 3) q).symm) y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      blowupPullbackCoefficient (G.embedding k) q a b (t, y) := by
  have hf := ((G.embedding k).forward_smooth t ht).contMDiffAt
    ((G.exhaustion.space_open k).mem_nhds hspace)
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hy)
  have hd := mfderiv_comp y (hf.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  simp only [blowupPullbackCoefficient, ht, dif_pos]
  change (rescaledMetric _ _ (S.base_scalar_pos (G.subsequence k))).inner _
    (mfderiv (𝓡 3) (𝓡 3)
      ((G.embedding k).forward t ht ∘ (extChartAt (𝓡 3) q).symm) y _)
    (mfderiv (𝓡 3) (𝓡 3)
      ((G.embedding k).forward t ht ∘ (extChartAt (𝓡 3) q).symm) y _) = _
  rw [hd, rescaledMetric_inner]
  rfl






theorem blowup_tendstoUniformlyOn_slice_pullbackJet
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (q : G.limit.carrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (htime : ∀ i, t ∈ Icc (-G.exhaustion.time (sigma i)) 0)
    (r : ℕ) (a b : Fin 3) :
    let gk := fun i => rescaledMetric
      ((S.flow (G.subsequence (sigma i))).metric
        ((S.base (G.subsequence (sigma i))).1 + t / S.scale (G.subsequence (sigma i))))
      (S.scale (G.subsequence (sigma i))) (S.base_scalar_pos (G.subsequence (sigma i)))
    let phi := fun i => (G.embedding (sigma i)).forward t (htime i) ∘
      (extChartAt (𝓡 3) q).symm
    TendstoUniformlyOn
      (fun i y => iteratedFDeriv ℝ r (fun z => (gk i).pullbackCoefficients (phi i) z
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) y)
      (fun y => iteratedFDeriv ℝ r
        (fun z => (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm z
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) y)
      atTop K := by
  dsimp only
  have hc := (continuousOn_extChartAt_symm q).mono hKc
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G (hK.image_of_continuousOn hc)
  have hdom : ({t} ×ˢ K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) ⊆
      {z | z ∈ blowupMetricChartDomain G.limit q ∧
        (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion.space j} := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    have hst : s = t := hs
    subst s
    exact ⟨⟨ht, hKc hy⟩, hj (mem_image_of_mem _ hy)⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hjN, hN⟩ := blowup_uniform_spatial_metricJets G q j r ({t} ×ˢ K)
    (isCompact_singleton.prod hK) hdom epsilon hepsilon
  filter_upwards [hsigma.eventually (eventually_ge_atTop N)] with i hi y hy
  have hspace : (extChartAt (𝓡 3) q).symm y ∈ G.exhaustion.space (sigma i) :=
    G.exhaustion.space_increasing (hjN.trans hi) (hj (mem_image_of_mem _ hy))
  have hopen : IsOpen ((extChartAt (𝓡 3) q).target ∩
      (extChartAt (𝓡 3) q).symm ⁻¹' G.exhaustion.space (sigma i)) :=
    (continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion.space_open (sigma i))
  have heq : (fun z => (rescaledMetric
      ((S.flow (G.subsequence (sigma i))).metric
        ((S.base (G.subsequence (sigma i))).1 + t / S.scale (G.subsequence (sigma i))))
      (S.scale (G.subsequence (sigma i)))
      (S.base_scalar_pos (G.subsequence (sigma i)))).pullbackCoefficients
        ((G.embedding (sigma i)).forward t (htime i) ∘ (extChartAt (𝓡 3) q).symm) z
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
      =ᶠ[𝓝 y] fun z => blowupPullbackCoefficient (G.embedding (sigma i)) q a b (t, z) := by
    filter_upwards [hopen.mem_nhds ⟨hKc hy, hspace⟩] with z hz
    exact slice_pullbackCoefficient_eq G (sigma i) t (htime i) q z hz.1 hz.2 a b
  rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
  have h := (hN (sigma i) hi).2 a b (t, y) ⟨rfl, hy⟩
  rw [dist_comm, dist_eq_norm]
  exact h

end PoincareConjecture.M32
