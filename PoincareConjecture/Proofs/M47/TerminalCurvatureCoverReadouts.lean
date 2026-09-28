import PoincareConjecture.Proofs.M47.TerminalCurvatureCoverField
import PoincareConjecture.Proofs.M47.TerminalCurvatureComponentField
import PoincareConjecture.Proofs.M47.TerminalCurvatureOrientationCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.ComponentCover
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

open RicciFlow.Splitting Poincare.Geometry.Manifold.RegularLevel



theorem terminalCurvature_connected_cover_readouts
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (cover : NullOrientationCover D) (p : UnitRicciKernel D) :
    letI := unitRicciKernelChartedSpace D cover.covering
    letI := unitRicciKernelIsManifold D cover.covering
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
    let gC := (unitRicciKernelMetric D cover.covering).connectedComponentMetric p
    let W := mpullback (𝓡 3) (𝓡 3) (Subtype.val : C → UnitRicciKernel D)
      (terminalCurvatureOrientedField D cover.covering)
    let projection := fun q : C => unitRicciKernelProjection D q.val
    ∀ q : C,
      (∀ v w : TangentSpace (𝓡 3) q, gC.inner q v w = g.inner (projection q)
        (mfderiv (𝓡 3) (𝓡 3) projection q v) (mfderiv (𝓡 3) (𝓡 3) projection q w)) ∧
      (∀ v w : TangentSpace (𝓡 3) q,
        gC.leviCivitaData.curvatureTensor q v w v w = D.curvatureTensor (projection q)
          (mfderiv (𝓡 3) (𝓡 3) projection q v) (mfderiv (𝓡 3) (𝓡 3) projection q w)
          (mfderiv (𝓡 3) (𝓡 3) projection q v) (mfderiv (𝓡 3) (𝓡 3) projection q w)) ∧
      gC.leviCivitaData.ricci q (W q) (W q) = 0 ∧
      gC.leviCivitaData.curvatureTensorNorm q = D.curvatureTensorNorm (projection q) := by
  let := unitRicciKernelChartedSpace D cover.covering
  let := unitRicciKernelIsManifold D cover.covering
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let g' := unitRicciKernelMetric D cover.covering
  let gC := g'.connectedComponentMetric p
  let W0 := terminalCurvatureOrientedField D cover.covering
  let W := mpullback (𝓡 3) (𝓡 3) (Subtype.val : C → UnitRicciKernel D) W0
  let projection := fun q : C => unitRicciKernelProjection D q.val
  have hproj := unitRicciKernelProjection_isLocalDiffeomorph D cover.covering
  have hi := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) C
  have hlocal := unitRicciKernelComponent_projection_isLocalDiffeomorph D cover.covering p
  have hd (q : C) (v : EuclideanSpace ℝ (Fin 3)) :
      mfderiv (𝓡 3) (𝓡 3) projection q v =
        mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) q.val v := by
    have hh := mfderiv_comp q ((hproj q.val).mdifferentiableAt (by simp))
      ((hi q).mdifferentiableAt (by simp))
    have he := congrArg (fun L => L v) hh
    change mfderiv (𝓡 3) (𝓡 3) projection q v =
      mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) q.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : C → UnitRicciKernel D) q v) at he
    rw [mfderiv_opens_subtypeVal_apply] at he
    exact he
  have hm (q : C) (v w : TangentSpace (𝓡 3) q) :
      gC.inner q v w = g.inner (projection q)
        (mfderiv (𝓡 3) (𝓡 3) projection q v) (mfderiv (𝓡 3) (𝓡 3) projection q w) := by
    change g'.inner q.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : C → UnitRicciKernel D) q v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : C → UnitRicciKernel D) q w) = _
    rw [mfderiv_opens_subtypeVal_apply, mfderiv_opens_subtypeVal_apply, hd, hd]
    rfl
  have hpush (q : C) : mfderiv (𝓡 3) (𝓡 3) projection q (W q) = q.val.val.snd := by
    have hinv : (mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) q.val).IsInvertible :=
      ⟨hproj.mfderivToContinuousLinearEquiv (by simp) q.val, rfl⟩
    rw [hd, show W q = W0 q.val from terminalCurvature_open_mpullback C W0 q]
    exact hinv.self_apply_inverse _
  dsimp only
  intro q
  refine ⟨hm q, ?_, ?_, ?_⟩
  · intro v w
    exact gC.leviCivitaData.curvatureTensor_eq_of_local_isometry D isOpen_univ
      hlocal.contMDiff.contMDiffOn (fun y _ => hm y) (mem_univ q) v w v w
  · have he := gC.leviCivitaData.ricci_eq_of_local_isometry D isOpen_univ
      hlocal.contMDiff.contMDiffOn (fun y _ => hm y) (mem_univ q) (W q) (W q)
    rw [hpush] at he
    exact he.trans (q.val.property.2 q.val.val.snd)
  · exact gC.leviCivitaData.curvatureTensorNorm_eq_of_local_isometry D isOpen_univ
      hlocal.contMDiff.contMDiffOn (fun y _ => hm y) (mem_univ q)

end PoincareConjecture.M47
