import PoincareLib.Topology.Manifold.NeckCap.Regions
import PoincareLib.Topology.Manifold.NeckCap.Separation

/-!
# Corrected neck and cap topology theory

Adapted from Mapher, `PoincareMT/Statements/Ch09/NeckCapTopology.lean`,
`PoincareMT/Definitions/M25NeckCapTopology.lean`, and
`PoincareMT/Statements/M25NeckCapTopology.lean`, commit
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained.
The four Appendix A conclusions share one threshold fixed before choosing
the manifold, metric, and cover.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

structure CorrectedA19Conclusion (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g) where
  tube : EpsilonTubeCertificate g H.X
  epsilon_eq : tube.epsilon = H.epsilon
  source_subset : tube.chain.source_necks ⊆ H.necks
  selected_centers_mem : ∀ i ∈ tube.chain.shape.active,
    (tube.chain.neck i).center ∈ H.X
  contains_X : H.X ⊆ tube.carrier
  separating_necks : ∀ N ∈ H.necks, N.IsSeparating

/-!
The two uniform neck-label fields below are project-strengthened obligations.
Appendix A.20 supplies the tube/fibration alternatives; the uniform
separating or nonseparating labels require the additional prime-decomposition
and Appendix A.18 chain argument recorded in the M25 review contract. They
are retained because the current downstream interface does not consume them
as direct A.20 conclusions.
-/
inductive CorrectedA20Conclusion (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g)
  | tube (certificate : EpsilonTubeCertificate g H.X)
      (source_subset : certificate.chain.source_necks ⊆ H.necks)
      (selected_centers_mem : ∀ i ∈ certificate.chain.shape.active,
        (certificate.chain.neck i).center ∈ H.X)
      (epsilon_eq : certificate.epsilon = H.epsilon)
      (carrier_eq_univ : certificate.carrier = Set.univ)
      (separating_necks : ∀ N ∈ H.necks, N.IsSeparating)
  | fibration (certificate : SphereBundleCircleCertificate g H.X)
      (carrier_eq_univ : certificate.carrier = Set.univ)
      (epsilon_eq : certificate.epsilon = H.epsilon)
      (nonseparating_necks : ∀ N ∈ H.necks, N.IsNonseparating)

def AppendixA21Theory (g : RiemannianMetric 3 M)
    (H : ConnectedNeckCapCover g) : Prop :=
  Nonempty {R : NeckCapRegion g H.X // NeckCapRegionCompatible g H R}

def AppendixA19Theory (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g)
    (_hsep : ∀ N ∈ H.necks, N.IsSeparating) : Prop :=
  Nonempty (CorrectedA19Conclusion g H)

def AppendixA20Theory (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g) (_hwhole : H.X = Set.univ) : Prop :=
  Nonempty (CorrectedA20Conclusion g H)

def AppendixA25Theory (g : RiemannianMetric 3 M)
    (H : ConnectedNeckCapCover g) (_hwhole : H.isWhole) : Prop :=
  Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant)

structure NeckCapTopologyTheory (g : RiemannianMetric 3 M) where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  a19 : ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon₀ →
    ∀ hsep, AppendixA19Theory g H hsep
  a20 : ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon₀ →
    ∀ hwhole : H.X = Set.univ, AppendixA20Theory g H hwhole
  a21 : ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon₀ →
    AppendixA21Theory g H
  a25 : ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon₀ →
    ∀ hwhole, AppendixA25Theory g H hwhole

/-- The epsilon threshold is fixed before any manifold, metric, or cover is
chosen.  A local `NeckCapTopologyTheory g` supplies the four conclusions for
one selected metric at this same universal threshold. -/
structure UniversalNeckCapTopologyTheory where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  local_theory : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∃ H : NeckCapTopologyTheory g, H.epsilon₀ = epsilon₀

/-- A local neck/cap output retains its region branch and compatibility bounds. -/
structure RepairedNeckCapTopologyData
    (g : RiemannianMetric 3 M) (H : ConnectedNeckCapCover g) where
  region : NeckCapRegion g H.X
  compatible : NeckCapRegionCompatible g H region

structure RepairedNeckCapTopologyTheory where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  /-- Corrected Proposition A.19: separating central spheres produce a tube. -/
  a19 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : NeckOnlyCover g, H.epsilon ≤ epsilon₀ →
        ∀ hsep, AppendixA19Theory g H hsep
  /-- Corrected Lemma A.20: the separating branch is a tube and the
      nonseparating branch is an S²-bundle over the circle.
      The uniform labels on all input necks also use Proposition A.11(5),
      pp. 503-504: nearby centered necks have ambient-isotopic central
      spheres, so separation is locally constant. The whole connected
      center cover makes it constant on all `H.necks`. Include A.11's
      smallness bound in the universal threshold. This additional argument
      belongs to M25's proof obligation; see
      `reviews/contracts/2026-09-20-m25-uniform-separation.md`. -/
  a20 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : NeckOnlyCover g, H.epsilon ≤ epsilon₀ →
        ∀ hwhole : H.X = Set.univ, AppendixA20Theory g H hwhole
  /-- Proposition A.21: a compatible local cap/neck region. -/
  a21 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ epsilon₀ →
        Nonempty (RepairedNeckCapTopologyData g H)
  /-- Proposition A.25: the four global cap/neck alternatives. -/
  a25 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ epsilon₀ → H.isWhole →
        Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant)

end PoincareMT
