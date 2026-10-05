/-
Adapted from AxelWorkspace, revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source: MorganTianLib/Bridges/CompatibleTransitions.lean.
Apache-2.0; see references/analysis/axel-workspace/LICENSE.Apache-2.0.txt.
-/

import PoincareLib.Topology.MetricSpace.GromovHausdorff.Limit.Compatible
import PoincareLib.Topology.MetricSpace.GromovHausdorff.Pointed.CompactDefiniteness

/-!
# marked transition extraction

Independent compact pointed limits at two consecutive radii become a genuine
transition map once their common source sequence has zero pointed distance and
the compact target distance is attained.  This file packages that extraction
without hiding either the common-limit or attainment hypotheses.
-/

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Extract a compatible pointed compact system from independently
obtained consecutive compact limits.  The map `embed n` places the inner limit
in the next stage; the extracted based isometry identifies the inner limit with
the current stage. -/
def ofCommonLimits
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (hattain : ∀ n, ∃ R : PointedGHRealization
      (stage n).toFiniteDiameterBasedMetricSpace
      (inner n).toFiniteDiameterBasedMetricSpace,
      pointedGHDistance
          (stage n).toFiniteDiameterBasedMetricSpace
          (inner n).toFiniteDiameterBasedMetricSpace =
        pointedHausdorffDist R)
    (embed : ∀ n, (inner n).carrier → (stage (n + 1)).carrier)
    (embed_isometry : ∀ n, Isometry (embed n))
    (embed_base : ∀ n, embed n (inner n).base = (stage (n + 1)).base) :
    CompatiblePointedCompactSystem.{u} := by
  have h_exists (n : ℕ) :
      ∃ e : (stage n).toFiniteDiameterBasedMetricSpace.carrier ≃ᵢ
          (inner n).toFiniteDiameterBasedMetricSpace.carrier,
        e (stage n).toFiniteDiameterBasedMetricSpace.base =
          (inner n).toFiniteDiameterBasedMetricSpace.base := by
    letI : CompactSpace
        (stage n).toFiniteDiameterBasedMetricSpace.carrier :=
      (stage n).compact
    letI : CompactSpace
        (inner n).toFiniteDiameterBasedMetricSpace.carrier :=
      (inner n).compact
    exact exists_basedIsometry_of_common_pointedGH_limit_of_attained
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace
      (inner n).toFiniteDiameterBasedMetricSpace
      (hstage n) (hinner n) (hattain n)
  choose e he using h_exists
  exact
    { stage := stage
      transition := fun n x =>
        embed n ((e n) (show
          (stage n).toFiniteDiameterBasedMetricSpace.carrier from x))
      transition_isometry := fun n => by
        change Isometry (embed n ∘ e n)
        exact (embed_isometry n).comp (e n).isometry
      transition_base := fun n => by
        simp only [Function.comp_apply]
        change embed n
          ((e n) ((stage n).toFiniteDiameterBasedMetricSpace.base)) =
            (stage (n + 1)).base
        rw [he n]
        exact embed_base n }

/-! The compact pointed-definiteness producer removes the need to pass an
explicit realization attaining each pointed distance.  The older constructor
above is retained for callers that already have such realizations. -/

/-- **Math.** Extract a compatible pointed compact system from common compact
pointed-GH limits without an explicit attainment premise.  Compactness of the
two stage carriers and the common source limits supply the based isometry at
each stage; the supplied inner-to-next-stage embedding supplies the transition.
-/
noncomputable def ofCommonLimits_of_compact_limits
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (embed : ∀ n, (inner n).carrier → (stage (n + 1)).carrier)
    (embed_isometry : ∀ n, Isometry (embed n))
    (embed_base : ∀ n, embed n (inner n).base = (stage (n + 1)).base) :
    CompatiblePointedCompactSystem.{u} := by
  have h_exists (n : ℕ) :
      ∃ e : (stage n).toFiniteDiameterBasedMetricSpace.carrier ≃ᵢ
          (inner n).toFiniteDiameterBasedMetricSpace.carrier,
        e (stage n).toFiniteDiameterBasedMetricSpace.base =
          (inner n).toFiniteDiameterBasedMetricSpace.base := by
    letI : CompactSpace
        (stage n).toFiniteDiameterBasedMetricSpace.carrier :=
      (stage n).compact
    letI : CompactSpace
        (inner n).toFiniteDiameterBasedMetricSpace.carrier :=
      (inner n).compact
    exact exists_basedIsometry_of_common_pointedGH_limit
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace
      (inner n).toFiniteDiameterBasedMetricSpace
      (hstage n) (hinner n)
  choose e he using h_exists
  exact
    { stage := stage
      transition := fun n x =>
        embed n ((e n) (show
          (stage n).toFiniteDiameterBasedMetricSpace.carrier from x))
      transition_isometry := fun n => by
        change Isometry (embed n ∘ e n)
        exact (embed_isometry n).comp (e n).isometry
      transition_base := fun n => by
        simp only [Function.comp_apply]
        change embed n
          ((e n) ((stage n).toFiniteDiameterBasedMetricSpace.base)) =
            (stage (n + 1)).base
        rw [he n]
        exact embed_base n }

/-- **Math.** Compose the consecutive transitions from stage `n` through stage
`n + k`.  The zero-step map is the identity, and each positive step appends
the next transition in the compatible compact system. -/
def transitionChain (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    (S.stage n).carrier → (S.stage (n + k)).carrier :=
  match k with
  | 0 => id
  | k + 1 => S.transition (n + k) ∘ transitionChain S n k

/-- **Math.** Every finite transition chain is an isometric embedding. -/
theorem transitionChain_isometry
    (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    Isometry (S.transitionChain n k) := by
  induction k with
  | zero => exact isometry_id
  | succ k ih =>
      exact (S.transition_isometry (n + k)).comp ih

/-- **Math.** A finite transition chain carries the basepoint of its initial
stage to the basepoint of its terminal stage. -/
theorem transitionChain_base
    (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    S.transitionChain n k (S.stage n).base = (S.stage (n + k)).base := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change S.transition (n + k) (S.transitionChain n k (S.stage n).base) =
        (S.stage (n + k + 1)).base
      rw [ih, S.transition_base]

/-! The same finite-chain factorization is useful before passing to the
completion.  Keeping it at the inductive-limit level exposes the exact
coherence relation used by the completed embedding. -/

/-- **Math.** The inductive-limit map from a terminal stage agrees with the
initial stage map after precomposition by a finite transition chain. -/
theorem stageMap_comp_transitionChain
    (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    S.stageMap (n + k) ∘ S.transitionChain n k =
      S.stageMap n := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change S.stageMap (n + k + 1) ∘
          (S.transition (n + k) ∘ S.transitionChain n k) =
        S.stageMap n
      rw [← Function.comp_assoc, S.stageMap_succ_comp_transition, ih]

/-- **Math.** The completed common-ambient embedding is unchanged after any
finite transition chain. -/
theorem stageEmbedding_comp_transitionChain
    (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    S.stageEmbedding (n + k) ∘ S.transitionChain n k =
      S.stageEmbedding n := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change S.stageEmbedding (n + k + 1) ∘
          (S.transition (n + k) ∘ S.transitionChain n k) =
        S.stageEmbedding n
      rw [← Function.comp_assoc, S.stageEmbedding_succ_comp_transition, ih]

/-- **Math.** A finite transition chain factors through every intermediate stage
after embedding both sides into the completed common ambient space. -/
theorem transitionChain_comp
    (S : CompatiblePointedCompactSystem.{u}) (n k l : ℕ) :
    S.stageEmbedding (n + (k + l)) ∘ S.transitionChain n (k + l) =
      S.stageEmbedding (n + k + l) ∘
        S.transitionChain (n + k) l ∘ S.transitionChain n k := by
  calc
    S.stageEmbedding (n + (k + l)) ∘ S.transitionChain n (k + l) =
        S.stageEmbedding n := stageEmbedding_comp_transitionChain S n (k + l)
    _ = S.stageEmbedding (n + k) ∘ S.transitionChain n k :=
      (stageEmbedding_comp_transitionChain S n k).symm
    _ = S.stageEmbedding (n + k + l) ∘
          S.transitionChain (n + k) l ∘ S.transitionChain n k := by
      symm
      rw [← Function.comp_assoc, stageEmbedding_comp_transitionChain]

end CompatiblePointedCompactSystem

#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.ofCommonLimits_of_compact_limits

end Poincare.GromovHausdorff
