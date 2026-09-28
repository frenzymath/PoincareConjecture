import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckCenterConnector
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.NeckRestriction











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28




theorem exists_source_neck_compact_core_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 256 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ →
        ∃ hle : N.epsilon ≤ 64 * N.epsilon,
          ∃ hhalf : 64 * N.epsilon < 1 / 2,
            let K := N.restrict_m28 (64 * N.epsilon) hle hhalf
            IsCompact (closure K.carrier) ∧
              closure K.carrier ⊆
                g.ball N.center (N.scale * N.epsilon⁻¹ / 16) := by
  let epsilon₀ := min (1 / 256 : ℝ) (1 / (512 * standardSpherePathCeiling + 1))
  have hL : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  refine ⟨epsilon₀, lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro M _ _ _ _ g N hsmall
  have hle : N.epsilon ≤ 64 * N.epsilon := by linarith [N.epsilon_pos]
  have hhalf : 64 * N.epsilon < 1 / 2 := by
    have h := hsmall.trans (min_le_left _ _)
    linarith
  refine ⟨hle, hhalf, ?_⟩
  let K := N.restrict_m28 (64 * N.epsilon) hle hhalf
  let R : ℝ := N.scale * N.epsilon⁻¹
  have hR : 0 < R := mul_pos N.scale_pos (inv_pos.mpr N.epsilon_pos)
  have hinv : 512 * standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos
      (hsmall.trans (min_le_right _ _))
    simpa only [one_div_one_div, one_div, inv_inv] using h
  have hbudget : (2 * (64 * N.epsilon)⁻¹ + 4 * standardSpherePathCeiling) *
      N.scale ≤ (5 / 128 : ℝ) * R := by
    calc
      _ ≤ ((5 / 128 : ℝ) * N.epsilon⁻¹) * N.scale := by
        apply mul_le_mul_of_nonneg_right _ N.scale_pos.le
        rw [mul_inv_rev]
        norm_num
        linarith
      _ = (5 / 128 : ℝ) * R := by dsimp [R]; ring
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) M
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hdist (x : M) (hx : x ∈ K.carrier) :
      g.edist N.center x < ENNReal.ofReal ((5 / 128 : ℝ) * R) := by
    obtain ⟨γ, h0, h1, hγ, _, hlength⟩ := exists_neck_center_connector K hx
    have hd : g.edist x K.center ≤ g.pathELength γ 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one
    have hlength' : g.pathELength γ 0 1 <
        ENNReal.ofReal ((5 / 128 : ℝ) * R) :=
      hlength.trans_le (ENNReal.ofReal_le_ofReal hbudget)
    change g.edist N.center x < _
    have hcomm : g.edist N.center x = g.edist x K.center :=
      Manifold.riemannianEDist_comm
    rw [hcomm]
    exact hd.trans_lt hlength'
  have hclosed : IsClosed {x : M |
      g.edist N.center x ≤ ENNReal.ofReal ((5 / 128 : ℝ) * R)} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hclosure : closure K.carrier ⊆ {x : M |
      g.edist N.center x ≤ ENNReal.ofReal ((5 / 128 : ℝ) * R)} :=
    closure_minimal (fun x hx => (hdist x hx).le) hclosed
  have hball : closure K.carrier ⊆ g.ball N.center (R / 16) := by
    intro x hx
    exact (hclosure hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (by positivity : 0 < R / 16)).mpr (by linarith))
  have houter : closure K.carrier ⊆ closure (g.ball N.center (R / 8)) := by
    intro x hx
    apply subset_closure
    exact (hball hx).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hcompact := (N.precompact_ball_of_central_sphere N.center_on_central_sphere).1
  exact ⟨hcompact.of_isClosed_subset isClosed_closure houter, hball⟩

end PoincareConjecture.M28
