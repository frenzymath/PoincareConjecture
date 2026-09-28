import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Gluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

theorem controlledCylinder_backward_step_of_strongNecks
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilonStar K : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧ 0 < K ∧
      ∀ {M B c : ℝ}, 0 < M → 0 ≤ B → K * M ≤ B →
        0 < c → c ≤ 1 / (4 * M) →
      ∀ {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T a eta etaOld : ℝ},
        0 < A → 0 < eta →
      ∀ (old : ControlledBlowupCylinder S k (A + 1) T B etaOld),
        IsCompact (closure (S.baseBall k A)) → generalizedPinchedOrNonnegative (S.flow k) →
        Real.exp (4 + M / (2 * eta)) / eta ≤ S.scale k →
      ∀ (hTc : c ≤ T) (ha : -T < a) (hac : a ≤ -T + c),
        (∀ s hs x, x ∈ S.baseBall k (A + 1) →
          (S.flow k).scalar (old.embedding.pointMap s hs x) ≤ M * S.scale k) →
        (∀ x ∈ closure (S.baseBall k A), ∃ epsilon, epsilon ≤ epsilonStar ∧
          ∃ N : GeneralizedStrongNeck (S.flow k) ((S.base k).1 + a / S.scale k) epsilon,
            N.center = old.embedding.forward a ⟨ha.le, by linarith⟩ x) →
        ∃ next : ControlledBlowupCylinder S k A (T + c) B eta,
          ∀ s hs x, x ∈ S.baseBall k A →
            (S.flow k).scalar (next.embedding.pointMap s hs x) ≤ M * S.scale k := by
  obtain ⟨epsilonStar, K, heps, hepsSmall, hK, hextend⟩ :=
    exists_cylinder_backward_extension_of_strongNecks hM04
  refine ⟨epsilonStar, K, heps, hepsSmall, hK, ?_⟩
  intro M B c hM hB hKM hc hcM S k A T a eta etaOld hA heta old hcompact hbranch
    hlarge hTc ha hac hscalar hneck
  let g := (S.flow k).metric (S.base k).1
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : ((S.flow k).slice (S.base k).1).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : ((S.flow k).slice (S.base k).1).carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace ((S.flow k).slice (S.base k).1).carrier :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) _
  have hq : 0 < S.scale k := S.base_scalar_pos k
  have hsqrt : 0 < Real.sqrt (S.scale k) := Real.sqrt_pos.mpr hq
  have hr : 0 < A / Real.sqrt (S.scale k) := div_pos hA hsqrt
  have hr' : 0 < (A + 1) / Real.sqrt (S.scale k) := div_pos (by linarith) hsqrt
  have hU : IsOpen (S.baseBall k A) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hW : IsOpen (S.baseBall k (A + 1)) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hne : (S.baseBall k A).Nonempty := by
    refine ⟨(S.base k).2, ?_⟩
    change edist (S.base k).2 (S.base k).2 < ENNReal.ofReal (A / Real.sqrt (S.scale k))
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hr
  have hKW : closure (S.baseBall k A) ⊆ S.baseBall k (A + 1) := by
    have hclosure : closure (S.baseBall k A) ⊆
        {x | g.edist (S.base k).2 x ≤ ENNReal.ofReal (A / Real.sqrt (S.scale k))} := by
      apply closure_minimal
      · intro x hx
        exact (show g.edist (S.base k).2 x < ENNReal.ofReal (A / Real.sqrt (S.scale k))
          from hx).le
      · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
    intro x hx
    exact (hclosure hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr').mpr
      ((div_lt_div_iff_of_pos_right hsqrt).mpr (by linarith)))
  obtain ⟨e, heold, hescalar, hecurv⟩ := hextend hM hB hKM hc hcM old.embedding
    hU hW hne hcompact hKW hTc ha hac hscalar old.curvature_bound hneck
  let next : ControlledBlowupCylinder S k A (T + c) B eta := {
    embedding := e
    zero_identity := by
      intro hzero x hx
      have hzeroOld : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
      rw [heold 0 hzeroOld x hx]
      exact old.zero_identity hzeroOld x (hKW (subset_closure hx))
    curvature_bound := hecurv
    negative_curvature_bound := fun s hs x hx =>
      negativeCurvaturePart_le_of_pinched_scalar_bound hbranch hM hq heta hlarge
        (e.pointMap s hs x) (hescalar s hs x hx) }
  exact ⟨next, hescalar⟩

end PoincareConjecture.M32
