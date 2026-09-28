import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.Compatible
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.CompactDefiniteness

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem

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

def transitionChain (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    (S.stage n).carrier → (S.stage (n + k)).carrier :=
  match k with
  | 0 => id
  | k + 1 => S.transition (n + k) ∘ transitionChain S n k

theorem transitionChain_isometry
    (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    Isometry (S.transitionChain n k) := by
  induction k with
  | zero => exact isometry_id
  | succ k ih =>
      exact (S.transition_isometry (n + k)).comp ih

theorem transitionChain_base
    (S : CompatiblePointedCompactSystem.{u}) (n k : ℕ) :
    S.transitionChain n k (S.stage n).base = (S.stage (n + k)).base := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change S.transition (n + k) (S.transitionChain n k (S.stage n).base) =
        (S.stage (n + k + 1)).base
      rw [ih, S.transition_base]

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

end Poincare.GromovHausdorff
