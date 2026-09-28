import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.Local
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.AbsoluteContinuity.UniformLocalBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem sqrt_reducedLength_intrinsic_bound
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) {τ : ℝ} (hτ : 0 < τ) :
    |Real.sqrt (reducedLength K.flow 0 p x τ) - Real.sqrt (reducedLength K.flow 0 p y τ)| ≤
      (2 * Real.sqrt (3 / τ)) * ((K.flow.metric (0 - τ)).edist x y).toReal := by
  let g := K.flow.metric (0 - τ)
  have hcomplete : MetricComplete g := K.complete (0 - τ) (by linarith)
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hdist⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hcomplete x y
  let f : ℝ → ℝ := fun s => Real.sqrt (reducedLength K.flow 0 p (γ s) τ)
  let D : ℝ≥0 := Real.toNNReal ((2 * Real.sqrt (3 / τ)) * (g.edist x y).toReal)
  have hD : (D : ℝ) = (2 * Real.sqrt (3 / τ)) * (g.edist x y).toReal :=
    Real.coe_toNNReal _ (by positivity)
  have hlocal : ∀ t ∈ Icc (0 : ℝ) 1, ∃ U ∈ 𝓝[Icc (0 : ℝ) 1] t, LipschitzOnWith D f U := by
    intro t ht
    obtain ⟨U, hU, htU, hbound⟩ := P.sqrt_reducedLength_local_intrinsic_bound p (γ t) hτ
    have htI : t ∈ Ioo (-ε) (1 + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hpre : γ ⁻¹' U ∈ 𝓝 t :=
      (hγ.contMDiffAt htI).continuousAt.preimage_mem_nhds (hU.mem_nhds htU)
    refine ⟨γ ⁻¹' U ∩ Icc (0 : ℝ) 1,
      inter_mem (mem_nhdsWithin_of_mem_nhds hpre) self_mem_nhdsWithin,
      LipschitzOnWith.of_dist_le_mul ?_⟩
    intro s hs v hv
    have hb := hbound (γ s) hs.1 (γ v) hv.1
    have hd : (g.edist (γ s) (γ v)).toReal = |s - v| * (g.edist x y).toReal := by
      rw [hdist s hs.2 v hv.2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    change |f s - f v| ≤ _ at hb
    change dist (f s) (f v) ≤ _
    rw [Real.dist_eq, Real.dist_eq, hD]
    exact hb.trans_eq (by rw [hd]; ring)
  have h := Poincare.Analysis.abs_sub_le_of_uniform_local_lipschitz_on_interval
    (by norm_num : (0 : ℝ) ≤ 1) D hlocal
  simpa only [f, hγ0, hγ1, hD, sub_zero, mul_one, abs_sub_comm] using h

theorem reducedLength_intrinsic_upper_bound
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) {τ : ℝ} (hτ : 0 < τ) :
    reducedLength K.flow 0 p y τ ≤
      (Real.sqrt (reducedLength K.flow 0 p x τ) +
        (2 * Real.sqrt (3 / τ)) * ((K.flow.metric (0 - τ)).edist x y).toReal) ^ 2 := by
  have h := P.sqrt_reducedLength_intrinsic_bound p x y hτ
  have hxy := (abs_le.mp h).1
  have hx := Real.sqrt_nonneg (reducedLength K.flow 0 p x τ)
  have hy := Real.sqrt_nonneg (reducedLength K.flow 0 p y τ)
  have hd : 0 ≤ (2 * Real.sqrt (3 / τ)) * ((K.flow.metric (0 - τ)).edist x y).toReal := by positivity
  nlinarith [Real.sq_sqrt (P.reducedLength_pos p y τ hτ).le]

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
