import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.FlowRealization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
private theorem partialChart_isLocalDiffeomorph
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ Φ.source) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (fun x : U => Φ x) := by
  intro x
  exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) U x).comp (𝓡 n) M
    ⟨Φ, hU x.property, Set.eqOn_refl _ _⟩



def pullbackToPartialChart {J : Set ℝ} (F : RicciFlow n M J)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ Φ.source) : RicciFlow n U J :=
  F.pullbackWithConnection (fun x : U => Φ x) (partialChart_isLocalDiffeomorph Φ U hU)
    (fun t => ((F.metric t).pullbackOfLocalDiffeomorph (fun x : U => Φ x)
      (partialChart_isLocalDiffeomorph Φ U hU)).openEuclideanLeviCivitaData U)


theorem pullbackToPartialChart_inner {J : Set ℝ} (F : RicciFlow n M J)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ Φ.source)
    (t : ℝ) (x : U) (v w : TangentSpace (𝓡 n) x) :
    ((F.pullbackToPartialChart Φ U hU).metric t).inner x v w =
      (F.metric t).pullbackCoefficients Φ x v w := by
  have hid : mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n)) x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x) x = _
    exact mfderiv_extChartAt_self
  have hΦ := (Φ.contMDiffOn_toFun x (hU x.property)).contMDiffAt
    (Φ.open_source.mem_nhds (hU x.property))
  have hc := mfderiv_comp x (hΦ.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓡 n) (U := U) (n := ∞) x).mdifferentiableAt (by simp))
  have hc' : mfderiv (𝓡 n) (𝓡 n) (fun y : U => Φ y) x =
      mfderiv (𝓡 n) (𝓡 n) Φ (x : EuclideanSpace ℝ (Fin n)) := by
    ext a
    have ha := congrArg (fun A => A a) hc
    change mfderiv (𝓡 n) (𝓡 n) (fun y : U => Φ y) x a =
      mfderiv (𝓡 n) (𝓡 n) Φ (x : EuclideanSpace ℝ (Fin n))
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n)) x a) at ha
    rw [hid] at ha
    exact ha
  change (F.metric t).inner (Φ x)
    (mfderiv (𝓡 n) (𝓡 n) (fun y : U => Φ y) x v)
    (mfderiv (𝓡 n) (𝓡 n) (fun y : U => Φ y) x w) = _
  rw [hc']
  rfl



theorem exists_ancient_limit_of_partial_chart_coefficients
    {ρ : ℝ} (hρ : 0 < ρ) (Fseq : ℕ → RicciFlow n M (Iic 0))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ k, closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ (Φ k).source)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball 0 ρ)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall 0 ρ))
    (hsymm : ∀ t ≤ 0, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v)
    (hlower : ∀ t ≤ 0, ∀ x ∈ U, ∃ c : ℝ, 0 < c ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ B (t, x) v v)
    (hjet : ∀ r K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric z.1).pullbackCoefficients (Φ k) z.2)
          (Iic 0 ×ˢ closedBall 0 ρ))
        (iteratedFDerivWithin ℝ r B (Iic 0 ×ˢ closedBall 0 ρ)) atTop K) :
    ∃ F : RicciFlow n U (Iic 0), ∀ t ≤ 0, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      (F.metric t).inner x v w = B (t, x) v w := by
  have hUΦ (k : ℕ) : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ (Φ k).source :=
    (hU.trans ball_subset_closedBall).trans (hsource k)
  let Fchart (k : ℕ) := (Fseq k).pullbackToPartialChart (Φ k) U (hUΦ k)
  apply exists_of_ancient_halfCylinder_coefficients hρ U hU Fchart
    (fun k z => ((Fseq k).metric z.1).pullbackCoefficients (Φ k) z.2)
    B ?_ hB ?_ hsymm hlower hjet
  · intro k
    exact ((Fseq k).contDiffOn_pullbackCoefficients_within (Φ k).open_source
      (Φ k).contMDiffOn_toFun).mono (prod_mono subset_rfl (hsource k))
  · intro k t _ x v w
    exact pullbackToPartialChart_inner (Fseq k) (Φ k) U (hUΦ k) t x v w

end PoincareConjecture.RicciFlow
