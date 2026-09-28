import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceWholeNeckBackwardFamily
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.WholeNeckBackwardData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {W : CriticalBallSourcePacket H}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
    (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))}
  {sigma : ℕ → ℕ}
  {V : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    EpsilonNeck G.limitMetric}

def fixedDomain (_D : WholeNeckBackwardData H W G sigma V) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    TopologicalSpace.Opens G.limitCarrier.carrier := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  exact ⟨V.region (-(3 * epsilon⁻¹ / 5)) (3 * epsilon⁻¹ / 5),
    V.region_open _ _⟩

variable (D : WholeNeckBackwardData H W G sigma V)

theorem epsilon_pos (D : WholeNeckBackwardData H W G sigma V) : 0 < epsilon := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  have h := V.epsilon_pos
  rw [D.epsilon_limit] at h
  linarith

theorem center_mem_fixedDomain :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    V.center ∈ D.fixedDomain := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  have hwidth : 0 < 3 * epsilon⁻¹ / 5 := by
    have hepsilon := D.epsilon_pos
    positivity
  exact V.central_sphere_subset_region (neg_neg_of_pos hwidth) hwidth
    V.center_on_central_sphere

def criticalMap (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    D.fixedDomain → H.tubeCriticalRegion W.tube W.radius (D.sourceIndex k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  exact fun x => G.embedding (sigma (k + D.offset)) x.val

theorem criticalMap_localDiffeomorph (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (D.criticalMap k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro x
  have hx : x.val ∈ G.exhaustion (sigma (k + D.offset)) :=
    D.exhaustion k x.property.1
  exact (openSubtype_isLocalDiffeomorph D.fixedDomain x).comp
    (𝓡 3) (H.tubeCriticalRegion W.tube W.radius (D.sourceIndex k))
    (G.embedding_smooth (sigma (k + D.offset)) ⟨x.val, hx⟩)

def originalMap (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    D.fixedDomain →
      ((E (D.sourceIndex k + H.shift)).flow.slice
        (E (D.sourceIndex k + H.shift)).time).carrier := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  exact fun x => (D.criticalMap k x).val.val

theorem originalMap_localDiffeomorph (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (D.originalMap k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro x
  exact ((D.criticalMap_localDiffeomorph k x).comp
    (𝓡 3) (W.tube (D.sourceIndex k)).carrierOpen
    (openSubtype_isLocalDiffeomorph
      (H.tubeCriticalRegion W.tube W.radius (D.sourceIndex k))
      (D.criticalMap k x))).comp
        (𝓡 3) ((E (D.sourceIndex k + H.shift)).flow.slice
          (E (D.sourceIndex k + H.shift)).time).carrier
        (openSubtype_isLocalDiffeomorph (W.tube (D.sourceIndex k)).carrierOpen
          (D.criticalMap k x).val)

theorem originalMap_in_core (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ x : D.fixedDomain, D.originalMap k x ∈ (D.neck k).carrier ∧
      |((D.neck k).coordinate_inverse (D.originalMap k x)).2| <
        3 * epsilon⁻¹ / 4 := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro x
  exact D.capture k x.val x.property.1 (abs_lt.mpr x.property.2).le

def neckMap (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    D.fixedDomain → strongNeckOpen (D.neck k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  exact fun x => ⟨D.originalMap k x, (D.originalMap_in_core k x).1⟩

theorem neckMap_localDiffeomorph (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (D.neckMap k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro x
  have hi := openSubtype_isLocalDiffeomorph (strongNeckOpen (D.neck k))
    (D.neckMap k x)
  have hinverse := hi.localInverse_isLocalDiffeomorphAt
  apply ((D.originalMap_localDiffeomorph k x).comp
    (𝓡 3) (strongNeckOpen (D.neck k)) hinverse).congr_of_eventuallyEq
  filter_upwards [hi.localInverse_eventuallyEq_right.comp_tendsto
    (D.originalMap_localDiffeomorph k x).contMDiffAt.continuousAt] with y hy
  apply Subtype.ext
  exact hy.symm

end PoincareConjecture.M28.CounterexampleNeckFamily.WholeNeckBackwardData
