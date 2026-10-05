import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Limits.OrdinaryLimitTopology
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Statement

/-!
# Uniform actual neck-or-cap alternatives for ordinary ancient limits

M27 chooses its threshold and constant before the ordinary source,
sequence and ancient limit. The actual projective-plane exclusion permits
Corollary 9.94, and limit noncompactness excludes its compact branches.
Source: Morgan-Tian Corollary 9.94, p. 243, and Theorem 12.28,
pp. 323-324; limit-canonical-alternatives.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.M34

/-- One classification constant precedes every ordinary Euclidean source
and every choice of its actual ancient blow-up identification. At the
actual normalized limit base the only remaining alternatives are a strong
neck centered there or a quantitative cap whose core contains it. -/
theorem ordinaryChapter11_limit_neck_or_cap (P : RepairedKappaAlternativeTheory.{0}) :
    ∃ epsilonPrime : ℝ, 0 < epsilonPrime ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonPrime →
        ∃ C : ℝ, 0 < C ∧
          ∀ {I : SpacetimeInterval}
            (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) I.domain)
            (R : OrdinaryProductRicciGeometry F.metric I),
            let G := ordinaryChapter11Flow (I := I) (F := F) R
            ∀ (p : ℕ → G.point) (hpositive : ∀ k, 0 < G.scalar (p k))
              (hdiverges : Tendsto (fun k => G.scalar (p k)) atTop atTop)
              (Conv : GeneralizedBlowupConvergence
                (fixedFlowBlowupSequence G p hpositive hdiverges) (blowupBackwardInterval ⊤))
              {kappa : ℝ} (A : BlowupAncientKappaIdentification Conv.limit kappa),
              letI := Conv.limit.carrier.topologicalSpace
              letI := Conv.limit.carrier.measurableSpace
              letI := Conv.limit.carrier.borelSpace
              letI := Conv.limit.carrier.chartedSpace
              letI := Conv.limit.carrier.isManifold
              letI := Conv.limit.carrier.t2Space
              letI := Conv.limit.carrier.t3Space
              letI := Conv.limit.carrier.secondCountable
              letI := Conv.limit.connectedSpace
              (∃ N : StrongEvolvingNeck A.solution 0 epsilon, N.center = Conv.limit.base) ∨
                Nonempty (M27CanonicalCap A.solution 0 Conv.limit.base epsilon C) := by
  obtain ⟨epsilonPrime, hPrime, hclass⟩ := P.corollary_9_94
  refine ⟨epsilonPrime, hPrime, ?_⟩
  intro epsilon hepsilon hsmall
  obtain ⟨C, hC, hcanonical⟩ := hclass epsilon hepsilon hsmall
  refine ⟨C, hC, ?_⟩
  intro I F R
  dsimp only
  intro p hpositive hdiverges Conv kappa A
  let : TopologicalSpace Conv.limit.carrier.carrier := Conv.limit.carrier.topologicalSpace
  let : MeasurableSpace Conv.limit.carrier.carrier := Conv.limit.carrier.measurableSpace
  let : BorelSpace Conv.limit.carrier.carrier := Conv.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Conv.limit.carrier.carrier :=
    Conv.limit.carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ Conv.limit.carrier.carrier := Conv.limit.carrier.isManifold
  let : T2Space Conv.limit.carrier.carrier := Conv.limit.carrier.t2Space
  let : T3Space Conv.limit.carrier.carrier := Conv.limit.carrier.t3Space
  let : SecondCountableTopology Conv.limit.carrier.carrier := Conv.limit.carrier.secondCountable
  let : ConnectedSpace Conv.limit.carrier.carrier := Conv.limit.connectedSpace
  have hRP := ordinaryChapter11_limit_not_projectivePlaneLine (I := I) (F := F) R
    p hpositive hdiverges Conv A
  have hcompact := ordinaryChapter11_limit_not_compact (I := I) (F := F) R
    p hpositive hdiverges Conv
  have h := hcanonical A.solution hRP 0 le_rfl Conv.limit.base
  cases h with
  | neck N hcenter => exact Or.inl ⟨N, hcenter⟩
  | cap N => exact Or.inr ⟨N⟩
  | component N => exact False.elim (hcompact N.compact)
  | round N => exact False.elim (hcompact N.compact)

end PoincareMT.M34
