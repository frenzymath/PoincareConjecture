import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CanonicalConnectionDifferenceEvolution
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CanonicalFlowCurvature

/-!
# Uniform energy for the actual connection evolution

Actual curvature families supply the spatial representatives and their
regularity. The genuine time derivatives of the connection coordinates
therefore satisfy the uniform Young estimate, with one constant before
the domain, the two flows and the tested time. This is Morgan-Tian
Section 12.5, pp. 309-319 and the owned
canonical-connection-difference-rate derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Both the actual families and their fixed-model coordinates have nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

/-- Elliptic three-jet bounds control the actual scalar time derivatives
of the connection-difference energy, with a constant chosen before both
flows and their domain (Section 12.5, pp. 309-319). -/
theorem exists_uniform_actual_connection_energy_bound
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
        (R R' : ℝ → U → FS n),
        (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
        (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
        ∀ (t : ℝ), t ∈ interior J → t ∈ interior J' → ∀ p x : U,
          let B0 := (F.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
          let B1 := (F'.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
          let H := B0 (x : V n) - B1 (x : V n)
          let A : ℝ → FA n := fun s => CovariantDerivative.difference
            (F.connection s).connection (F'.connection s).connection x
          let S := fun y => R t ((extChartAt (𝓡 n) p).symm y) -
            R' t ((extChartAt (𝓡 n) p).symm y)
          (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 (x : V n)‖ ≤ M) →
          (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 (x : V n)‖ ≤ M) →
          (∀ v, a * ‖v‖ ^ 2 ≤ B0 (x : V n) v v) →
          (∀ v, a * ‖v‖ ^ 2 ≤ B1 (x : V n) v v) →
          ∀ ε : ℝ, 0 < ε →
            (∑ alpha : Fin dA, 2 * qA (A t) alpha *
              deriv (fun s => qA (A s) alpha) t) ≤
              ε * (∑ beta : Fin dS × Fin n,
                (fderiv ℝ (fun y => qS (S y) beta.1) (x : V n)
                  (EuclideanSpace.single beta.2 1)) ^ 2) +
                (C / ε + C) * ((∑ j, qH H j ^ 2) +
                  (∑ j, qA (A t) j ^ 2) + (∑ j, qS (S (x : V n)) j ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_canonicalDomain_connectionRate_bound qH qA qS ha M
  refine ⟨C, hC, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' R R' hR hR' t ht ht' p x B0 B1 H A S hj0 hj1 he0 he1 ε hε
  let R0 := fun y => R t ((extChartAt (𝓡 n) p).symm y)
  let R1 := fun y => R' t ((extChartAt (𝓡 n) p).symm y)
  have hc : ContDiffOn ℝ ∞ (fun y : V n => (t, y)) U :=
    contDiffOn_const.prodMk contDiffOn_id
  have hs0 : ContDiffOn ℝ ∞ R0 U :=
    (canonicalDomain_contDiffOn_flow_curvature U hU qS F R hR p).comp hc
      (fun _ hy => ⟨interior_subset ht, hy⟩)
  have hs1 : ContDiffOn ℝ ∞ R1 U :=
    (canonicalDomain_contDiffOn_flow_curvature U hU qS F' R' hR' p).comp hc
      (fun _ hy => ⟨interior_subset ht', hy⟩)
  have hd0 := (hs0.differentiableOn (by simp) (x : V n) x.property).differentiableAt
    (hU.mem_nhds x.property)
  have hd1 := (hs1.differentiableOn (by simp) (x : V n) x.property).differentiableAt
    (hU.mem_nhds x.property)
  have hr0 := fun y (_hy : y ∈ U) => canonicalDomain_raw_flow_curvature U hU F R hR p t y
  have hr1 := fun y (_hy : y ∈ U) => canonicalDomain_raw_flow_curvature U hU F' R' hR' p t y
  dsimp only [A]
  simp_rw [canonicalDomain_deriv_connection_difference_coordinate U hU qA qS
    F F' ht ht' p x R0 R1 hr0 hr1 hd0 hd1]
  exact hbound U hU hNE (F.metric t) (F.connection t) (F'.metric t) (F'.connection t)
    p (x : V n) x.property hj0 hj1 he0 he1
    (fun beta => fderiv ℝ (fun y => qS (S y) beta.1) (x : V n)
      (EuclideanSpace.single beta.2 1)) H (A t) (S (x : V n)) ε hε

end PoincareMT.M34
