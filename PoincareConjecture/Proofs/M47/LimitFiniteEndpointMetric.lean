import PoincareConjecture.Proofs.M47.LimitFiniteEndpointStageAgreement
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointStageFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteEndpointMetricTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointMetricCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointMetricManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

local notation "U" => (fun m : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space m) (G.exhaustion.space_open m))

theorem limitFinite_exists_endpoint_metric (d : ℕ → ℝ) (hd : ∀ m, 0 < d m)
    (A : ∀ m, RicciFlow 3 (U m) (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)))
    (hcompat : ∀ m n (y : G.limit.sliceCarrier.carrier)
      (hym : y ∈ U m) (hyn : y ∈ U n) (v w : E),
        ((A m).metric (-H.toReal)).inner ⟨y, hym⟩ v w =
          ((A n).metric (-H.toReal)).inner ⟨y, hyn⟩ v w) :
    (∀ m, -H.toReal ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)) ∧
      ∃ gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier,
        ∃ _DE : LeviCivitaData gE,
          ∀ m (x : U m) (v w : E), ((A m).metric (-H.toReal)).inner x v w =
            gE.inner x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w) := by
  classical
  have ht0 (m : ℕ) : -H.toReal ∈
      Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) :=
    ⟨by linarith [hd m], by linarith [hd m]⟩
  let q : ∀ m, U m → G.limit.sliceCarrier.carrier := fun _ => Subtype.val
  have hq (m : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q m) :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U m)
  have hcover : ∀ y, ∃ m x, q m x = y := by
    intro y
    have hy : y ∈ ⋃ m, G.exhaustion.space m := by
      rw [G.exhaustion.space_covers]
      exact mem_univ y
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    exact ⟨m, ⟨y, hm⟩, rfl⟩
  have hpair : ∀ m n (x : U m) (y : U n), q m x = q n y → ∀ a b c e : E,
      mfderiv (𝓡 3) (𝓡 3) (q m) x a = mfderiv (𝓡 3) (𝓡 3) (q n) y c →
      mfderiv (𝓡 3) (𝓡 3) (q m) x b = mfderiv (𝓡 3) (𝓡 3) (q n) y e →
      ((A m).metric (-H.toReal)).inner x a b = ((A n).metric (-H.toReal)).inner y c e := by
    intro m n x y hxy a b c e ha hb
    have ha' : a = c := by
      simpa only [q,
        Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply] using ha
    have hb' : b = e := by
      simpa only [q,
        Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply] using hb
    have hyn : x.val ∈ U n := (congrArg (fun z => z ∈ U n) hxy).mpr y.property
    have hy : (⟨x.val, hyn⟩ : U n) = y := Subtype.ext hxy
    have h := hcompat m n x.val x.property hyn a b
    rw [hy] at h
    exact h.trans (congrArg₂ (fun v w : E => ((A n).metric (-H.toReal)).inner y v w) ha' hb')
  obtain ⟨gE, hread, _huniq⟩ := exists_unique_metric_of_covering_local_diffeomorphisms
    (fun m => (A m).metric (-H.toReal)) q hq hcover hpair
  let DE : LeviCivitaData gE := gE.leviCivitaDataOfCover
    (fun m => (A m).metric (-H.toReal)) (fun m => (A m).connection (-H.toReal)) q
    (fun m => (hq m).contMDiff)
    (fun m x => ⟨(hq m x).mfderivToContinuousLinearEquiv (by simp), rfl⟩) hread hcover
  exact ⟨ht0, gE, DE, hread⟩

end PoincareConjecture.M47
