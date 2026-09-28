import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.SeedGluing
import PoincareConjecture.Proofs.M32.Claim11_35.FiniteSlabs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

theorem exists_controlled_seed_of_terminal_strongNecks
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilonSeed Kseed : ℝ, 0 < epsilonSeed ∧ epsilonSeed ≤ 1 / 200 ∧ 0 < Kseed ∧
      ∀ {S : GeneralizedBlowupSequence.{u}} {M B c : ℝ},
        0 < M → 0 ≤ B → Kseed * M ≤ B → 0 < c → c ≤ 1 / (4 * M) →
        (∀ k, generalizedPinchedOrNonnegative (S.flow k)) →
        BlowupBaseBallsCompact S →
        (∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.baseBall k A,
          (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ M * S.scale k) →
        (∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop, ∀ x ∈ closure (S.baseBall k A),
          ∃ epsilon, epsilon ≤ epsilonSeed ∧
            ∃ N : GeneralizedStrongNeck (S.flow k) (S.base k).1 epsilon,
              N.center = x) →
        ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
          (∃ e : ControlledBlowupCylinder S k A c B eta,
            (∀ s hs x, x ∈ S.baseBall k A →
              (S.flow k).scalar (e.embedding.pointMap s hs x) ≤ M * S.scale k) ∧
            (∀ s hs x, x ∈ S.baseBall k A → GeneralizedKappaNoncollapsedAt
              (S.flow k) (e.embedding.pointMap s hs x) neckNoncollapseConstant 1)) ∧
          Nonempty (M30FiniteHorizonSlab S k A c neckNoncollapseConstant 1) := by
  obtain ⟨epsilonSeed, Kseed, heps, hepsSmall, hK, hseed⟩ :=
    exists_seed_cylinder_of_terminal_strongNecks hM04
  refine ⟨epsilonSeed, Kseed, heps, hepsSmall, hK, ?_⟩
  intro S M B c hM hB hKM hc hcM hbranch hcompact hscalar hnecks A hA eta heta
  filter_upwards [hcompact A hA, hscalar (A + 1) (by linarith), hnecks A hA,
    S.scalar_diverges.eventually (eventually_ge_atTop
      (Real.exp (4 + M / (2 * eta)) / eta))] with k hkCompact hkScalar hkNecks hkScale
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
  obtain ⟨d, hzero, hscalarD, hcurvD, hnoncollapseD⟩ := hseed hM hB hKM hc hcM hq
    hU hW hne hkCompact hKW hkScalar hkNecks
  let e : ControlledBlowupCylinder S k A c B eta := {
    embedding := d
    zero_identity := hzero
    curvature_bound := hcurvD
    negative_curvature_bound := fun s hs x hx =>
      negativeCurvaturePart_le_of_pinched_scalar_bound (hbranch k) hM hq heta hkScale
        (d.pointMap s hs x) (hscalarD s hs x hx) }
  let slab : M30FiniteHorizonSlab S k A c neckNoncollapseConstant 1 := {
    embedding := restrictCylinderTime d Ioc_subset_Icc_self
    zero_identity := fun hz x hx => hzero (Ioc_subset_Icc_self hz) x hx
    noncollapsed := fun s hs x hx => hnoncollapseD s (Ioc_subset_Icc_self hs) x hx }
  exact ⟨⟨e, hscalarD, hnoncollapseD⟩, ⟨slab⟩⟩

end PoincareConjecture.M32
