import PoincareConjecture.Proofs.M47.TerminalCommonIntervalOriginalCoherence
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateMetric
import PoincareConjecture.Proofs.M13.Metric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCommonInterval_original_coordinate_coherence
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {C D : GeneralizedSliceCarrier.{u}}
    {origin Q t : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}
    (e : GeneralizedFlowCylinder H.generalized C origin Q I U)
    (f : GeneralizedFlowCylinder H.generalized D origin Q J V)
    (hIc : I.OrdConnected) (hJc : J.OrdConnected) (hU : IsOpen U) (hV : IsOpen V)
    (ht : t ≤ 0) (hI : Icc t 0 ⊆ I) (hJ : Icc t 0 ⊆ J)
    (a : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier E ∞)
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) D.carrier E ∞) :
    let e0 := e.spatialOpenPartialHomeomorph hU 0 (hI ⟨ht, le_rfl⟩)
    let f0 := f.spatialOpenPartialHomeomorph hV 0 (hJ ⟨ht, le_rfl⟩)
    let T := ((a.symm.toOpenPartialHomeomorph.trans e0).trans f0.symm).trans
      b.toOpenPartialHomeomorph
    let g : RiemannianMetric 3 (H.generalized.slice (origin + t / Q)).carrier :=
      M13.scaleSmoothMetric (H.generalized.metric (origin + t / Q)) Q e.scale_pos
    ContDiffOn ℝ ∞ T T.source ∧
      (∀ x ∈ T.source, e.forward t (hI ⟨le_rfl, ht⟩) (a.symm x) =
        f.forward t (hJ ⟨le_rfl, ht⟩) (b.symm (T x))) ∧
      ∀ x ∈ T.source, ∀ v w : E,
        g.pullbackCoefficients (f.forward t (hJ ⟨le_rfl, ht⟩) ∘ b.symm) (T x)
            (fderiv ℝ T x v) (fderiv ℝ T x w) =
          g.pullbackCoefficients (e.forward t (hI ⟨le_rfl, ht⟩) ∘ a.symm) x v w := by
  let e0 := e.spatialOpenPartialHomeomorph hU 0 (hI ⟨ht, le_rfl⟩)
  let f0 := f.spatialOpenPartialHomeomorph hV 0 (hJ ⟨ht, le_rfl⟩)
  let ed : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
      (H.generalized.slice (origin + 0 / Q)).carrier ∞ := {
    toPartialEquiv := e0.toPartialEquiv
    open_source := e0.open_source
    open_target := e0.open_target
    contMDiffOn_toFun := e.spatialOpenPartialHomeomorph_contMDiffOn hU 0 _
    contMDiffOn_invFun := e.spatialOpenPartialHomeomorph_symm_contMDiffOn hU 0 _ }
  let fd : PartialDiffeomorph (𝓡 3) (𝓡 3) D.carrier
      (H.generalized.slice (origin + 0 / Q)).carrier ∞ := {
    toPartialEquiv := f0.toPartialEquiv
    open_source := f0.open_source
    open_target := f0.open_target
    contMDiffOn_toFun := f.spatialOpenPartialHomeomorph_contMDiffOn hV 0 _
    contMDiffOn_invFun := f.spatialOpenPartialHomeomorph_symm_contMDiffOn hV 0 _ }
  let T := ((a.symm.trans ed).trans fd.symm).trans b
  let g : RiemannianMetric 3 (H.generalized.slice (origin + t / Q)).carrier :=
    M13.scaleSmoothMetric (H.generalized.metric (origin + t / Q)) Q e.scale_pos
  have hback := (terminalCommonInterval_original_cross_coherence H e f
    hIc hJc hU hV ht hI hJ).1
  have hb (x : E) (hx : x ∈ T.source) :
      b.symm (T x) = f0.symm (e0 (a.symm x)) := b.toPartialEquiv.left_inv hx.2
  have hmem (x : E) (hx : x ∈ T.source) : b.symm (T x) ∈ V := by
    rw [hb x hx]
    exact f0.map_target hx.1.2
  have hmaps (x : E) (hx : x ∈ T.source) :
      e.forward t (hI ⟨le_rfl, ht⟩) (a.symm x) =
        f.forward t (hJ ⟨le_rfl, ht⟩) (b.symm (T x)) := by
    rw [hb x hx]
    exact hback (a.symm x) ⟨hx.1.1.2, hx.1.2⟩
  refine ⟨contMDiffOn_iff_contDiffOn.mp T.contMDiffOn_toFun, hmaps, ?_⟩
  intro x hx v w
  have heq : (f.forward t (hJ ⟨le_rfl, ht⟩) ∘ b.symm) ∘ T =ᶠ[𝓝 x]
      e.forward t (hI ⟨le_rfl, ht⟩) ∘ a.symm := by
    filter_upwards [T.open_source.mem_nhds hx] with y hy
    exact (hmaps y hy).symm
  have hf := (f.forward_smooth t (hJ ⟨le_rfl, ht⟩)).contMDiffAt
    (hV.mem_nhds (hmem x hx))
  have hb' := b.contMDiffOn_invFun.contMDiffAt
    (b.open_target.mem_nhds (b.map_source hx.2))
  exact g.pullbackCoefficients_comp_of_eventuallyEq
    ((hf.comp (T x) hb').mdifferentiableAt (by simp))
    (mdifferentiableAt_iff_differentiableAt.mp (T.mdifferentiableAt (by simp) hx))
    heq v w

end PoincareConjecture.M47
