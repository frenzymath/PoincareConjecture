import PoincareConjecture.Proofs.M47.LimitNoncollapseMovingJets
import PoincareConjecture.Proofs.M47.LimitNoncollapseCurvature
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderCurvature
import PoincareConjecture.Proofs.M34.Standard.CoordinateScalarGerm










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace E C.limit.carrier.carrier := C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold



theorem limitNoncollapse_tendsto_moving_coordinate_curvature
    (P : M47Predecessors.{u}) (q : C.limit.sliceCarrier.carrier)
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKJ : Ktime ⊆ J)
    {index : ℕ → ℕ} (hindex : Tendsto index atTop atTop)
    {z : ℕ → ℝ × E} {p : ℝ × E}
    (htime : ∀ k, (z k).1 ∈ Ktime) (hp : p.1 ∈ Ktime)
    (hvalid : ∀ k, (z k).1 ∈ Icc (-C.exhaustion.time (index k)) 0)
    (hchart : p.2 ∈ (extChartAt (𝓡 3) q).target)
    (hz : Tendsto z atTop (𝓝 p)) :
    Tendsto (fun k => (S.flow (C.subsequence (index k))).curvatureNorm
      ((C.embedding (index k)).pointMap (z k).1 (hvalid k)
        ((extChartAt (𝓡 3) q).symm (z k).2)) / S.scale (C.subsequence (index k)))
      atTop (𝓝 ((C.limit.flow.connection p.1).curvatureTensorNorm
        ((extChartAt (𝓡 3) q).symm p.2))) := by
  classical
  let c := extChartAt (𝓡 3) q
  obtain ⟨H, hH, hpH, hHt⟩ := exists_compact_subset (isOpen_extChartAt_target q) hchart
  have hzH := (continuousAt_snd.tendsto.comp hz).eventually
    (mem_interior_iff_mem_nhds.mp hpH)
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset
    (hH.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hHt))
  have hdomain : ∀ᶠ k in atTop, (z k).2 ∈ c.target ∧
      c.symm (z k).2 ∈ C.exhaustion.space (index k) := by
    filter_upwards [hzH, hindex.eventually (eventually_ge_atTop j)] with k hk hjk
    exact ⟨hHt hk, C.exhaustion.space_increasing hjk (hj ⟨(z k).2, hk, rfl⟩)⟩
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := C.limit.carrier.exists_local_coordinate_realization
    (C.limit.flow.metric p.1) q p.1 p.2 hchart
  have hg := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  have hreal : ∀ᶠ k in atTop,
      ∃ gd : Σ g : RiemannianMetric 3 E, LeviCivitaData g,
        ∀ᶠ y in 𝓝 (z k).2, ∀ a b : Fin 3,
          gd.1.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) =
            blowupPullbackCoefficient (C.embedding (index k)) q a b ((z k).1, y) := by
    filter_upwards [hdomain] with k hk
    obtain ⟨gk, Dk, Vk, hVko, hzVk, _, heqk⟩ :=
      (C.embedding (index k)).exists_local_coordinate_realization
        (C.exhaustion.space_open (index k)) q (hvalid k) (z k).2 hk
    exact ⟨⟨gk, Dk⟩, Filter.Eventually.mono (hVko.mem_nhds hzVk) heqk⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hid (k : ℕ) : (gd k).1.pullbackCoefficients id = (gd k).1.euclideanCoefficients := by
    ext y v w
    simp +instances [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  have hjets (r : ℕ) (_hr : r ≤ 2) (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (gd k).1.pullbackCoefficients id y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
          (z k).2) atTop
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p.2)) := by
    simp_rw [hid]
    erw [C.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      q _ p.1 p.2 g hg r a b]
    apply (limitNoncollapse_tendsto_moving_spatial_jets C P q hKtime hKJ hindex
      htime hp hchart hz r a b).congr'
    filter_upwards [hgd] with k hk
    have he : (fun y => (gd k).1.euclideanCoefficients y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 (z k).2]
        (fun y => blowupPullbackCoefficient (C.embedding (index k)) q a b ((z k).1, y)) :=
      hk.mono (fun y hy => hy a b)
    exact (he.iteratedFDeriv ℝ r).self_of_nhds.symm
  have hn := limitNoncollapse_curvature_of_spatial_jets (fun k => (gd k).2)
    (fun _ => id) D (fun k => (z k).2) p.2
    (Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => by
      refine ⟨contMDiffAt_id, ?_⟩
      rw [mfderiv_id]
      exact Function.injective_id))) hjets
  rw [C.limit.carrier.curvatureTensorNorm_eq_of_coordinate_germ
    (C.limit.flow.metric p.1) (C.limit.flow.connection p.1) q p.1 p.2 hchart g D hg] at hn
  apply hn.congr'
  filter_upwards [hgd, hdomain] with k hk hdom
  exact ((C.embedding (index k)).curvatures_eq_of_coordinate_germ
    (C.exhaustion.space_open (index k)) q (hvalid k) (z k).2 hdom
    (gd k).1 (gd k).2 hk).2

end PoincareConjecture.M47
