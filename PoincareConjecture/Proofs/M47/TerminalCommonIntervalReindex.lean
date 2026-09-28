import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47

def terminalCommonInterval_reindex (V : GeneralizedBlowupSequence.{u})
    (sigma : ℕ → ℕ) (hsigma : StrictMono sigma) : GeneralizedBlowupSequence.{u} where
  flow k := V.flow (sigma k)
  base k := V.base (sigma k)
  base_scalar_pos k := V.base_scalar_pos (sigma k)
  scalar_diverges := V.scalar_diverges.comp hsigma.tendsto_atTop

def terminalCommonInterval_reindexCylinder
    {V : GeneralizedBlowupSequence.{u}} {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    {k : ℕ} {A T B eta : ℝ}
    (e : ControlledBlowupCylinder V (sigma k) A T B eta) :
    ControlledBlowupCylinder (terminalCommonInterval_reindex V sigma hsigma) k A T B eta where
  embedding := e.embedding
  zero_identity := e.zero_identity
  curvature_bound := e.curvature_bound
  negative_curvature_bound := e.negative_curvature_bound

def terminalCommonInterval_originalCylinder
    {V : GeneralizedBlowupSequence.{u}} {sigma : ℕ → ℕ} {hsigma : StrictMono sigma}
    {k : ℕ} {A T B eta : ℝ}
    (e : ControlledBlowupCylinder (terminalCommonInterval_reindex V sigma hsigma)
      k A T B eta) : ControlledBlowupCylinder V (sigma k) A T B eta where
  embedding := e.embedding
  zero_identity := e.zero_identity
  curvature_bound := e.curvature_bound
  negative_curvature_bound := e.negative_curvature_bound

theorem terminalCommonInterval_reindex_cylinder_iff
    {V : GeneralizedBlowupSequence.{u}} {sigma : ℕ → ℕ} {hsigma : StrictMono sigma}
    {k : ℕ} {A T B eta : ℝ} :
    Nonempty (ControlledBlowupCylinder (terminalCommonInterval_reindex V sigma hsigma)
      k A T B eta) ↔ Nonempty (ControlledBlowupCylinder V (sigma k) A T B eta) :=
  ⟨fun ⟨e⟩ => ⟨terminalCommonInterval_originalCylinder e⟩,
    fun ⟨e⟩ => ⟨terminalCommonInterval_reindexCylinder hsigma e⟩⟩

noncomputable def terminalCommonInterval_restrict
    {V : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T B eta A' T' B' eta' : ℝ}
    (e : ControlledBlowupCylinder V k A T B eta)
    (hA : A' ≤ A) (hT : T' ≤ T) (hB : B ≤ B') (heta : eta ≤ eta') :
    ControlledBlowupCylinder V k A' T' B' eta' := by
  have htime : Icc (-T') 0 ⊆ Icc (-T) 0 := Icc_subset_Icc (neg_le_neg hT) le_rfl
  have hspace : V.baseBall k A' ⊆ V.baseBall k A := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hA (Real.sqrt_nonneg _)))
  refine {
    embedding := e.embedding.restrict htime hspace
    zero_identity := fun h x hx => e.zero_identity (htime h) x (hspace hx)
    curvature_bound := ?_
    negative_curvature_bound := ?_ }
  · intro s hs x hx
    exact (e.curvature_bound s (htime hs) x (hspace hx)).trans
      (mul_le_mul_of_nonneg_right hB (V.base_scalar_pos k).le)
  · intro s hs x hx
    exact (e.negative_curvature_bound s (htime hs) x (hspace hx)).trans
      (mul_le_mul_of_nonneg_right heta (V.base_scalar_pos k).le)

theorem terminalCommonInterval_restrict_pointMap
    {V : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T B eta A' T' B' eta' : ℝ}
    (e : ControlledBlowupCylinder V k A T B eta)
    (hA : A' ≤ A) (hT : T' ≤ T) (hB : B ≤ B') (heta : eta ≤ eta')
    (s : ℝ) (hs : s ∈ Icc (-T') 0)
    (x : ((V.flow k).slice (V.base k).1).carrier) :
    (terminalCommonInterval_restrict e hA hT hB heta).embedding.pointMap s hs x =
      e.embedding.pointMap s ⟨(neg_le_neg hT).trans hs.1, hs.2⟩ x := rfl

def terminalCommonInterval_compSubsequence
    {V : GeneralizedBlowupSequence.{u}} {sigma : ℕ → ℕ}
    (hsigma : StrictMono sigma) {J : Set ℝ}
    (G : GeneralizedBlowupConvergence (terminalCommonInterval_reindex V sigma hsigma) J) :
    GeneralizedBlowupConvergence V J where
  limit := G.limit
  subsequence := sigma ∘ G.subsequence
  subsequence_strictMono := hsigma.comp G.subsequence_strictMono
  exhaustion := G.exhaustion
  embedding := G.embedding
  base_preserving := G.base_preserving
  source_balls_in_image := G.source_balls_in_image
  pullback_metric_CInfinity := G.pullback_metric_CInfinity

theorem terminalCommonInterval_reindex_compact
    {V : GeneralizedBlowupSequence.{u}} (h : BlowupBaseBallsCompact V)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) :
    BlowupBaseBallsCompact (terminalCommonInterval_reindex V sigma hsigma) := by
  intro A hA
  exact hsigma.tendsto_atTop.eventually (h A hA)

end PoincareConjecture.M47
