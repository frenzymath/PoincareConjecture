import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMotionTangent
import PoincareConjecture.Proofs.M09.FrameForms
import PoincareConjecture.Proofs.M04.RicciRegularity





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Set Filter Bundle MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}





theorem m64RicciQuadratic_continuousOn (D : LeviCivitaData g)
    {X : Type*} [TopologicalSpace X] {S : Set X} {v : X → TangentBundle (𝓡 n) M}
    (hv : ContinuousOn v S) :
    ContinuousOn (fun x => D.ricci (v x).proj (v x).snd (v x).snd) S := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  let p := (v x).proj
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  obtain ⟨hbase, hcoord⟩ :=
    (FiberBundle.continuousWithinAt_totalSpace (EuclideanSpace ℝ (Fin n)) v).mp (hv x hx)
  let z := fun y => e.symmL ℝ p (e (v y)).2
  have hz : ContinuousWithinAt z S x :=
    (e.symmL ℝ p).continuous.continuousAt.comp_continuousWithinAt hcoord
  have hR := M04.isSmoothCovariantTensor_ricciEvaluation D
  have hBreg := Proofs.M09.frameTensorForm_smooth g D.ricciEvaluation hR p
  have hBc : ContinuousOn (Proofs.M09.frameTensorForm g D.ricciEvaluation hR p)
      e.baseSet := hBreg.continuousOn
  have hB := (hBc.continuousAt (e.open_baseSet.mem_nhds hp)).comp_continuousWithinAt hbase
  have heval := (hB.clm_apply hz).clm_apply hz
  apply heval.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [hbase (e.open_baseSet.mem_nhds hp)] with y hy
  have hreconstruct : Proofs.M09.extensionMap p (v y).proj (z y) = (v y).snd := by
    change e.symmL ℝ (v y).proj
      (e.continuousLinearMapAt ℝ p (e.symmL ℝ p (e (v y)).2)) = (v y).snd
    rw [e.continuousLinearMapAt_symmL hp, e.symmL_apply hy]
    exact e.symm_apply_apply_mk hy (v y).snd
  rw [Function.comp_apply, Proofs.M09.frameTensorForm_apply, hreconstruct]
  rfl





theorem m64Annulus_modulusRicci_integrable (D : LeviCivitaData g) (r : ℝ)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain) :
    IntegrableOn (fun p =>
      r * D.ricci (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      r⁻¹ * D.ricci (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
      m64AnnulusDomain volume := by
  have hc (i : Fin 2) := m64RicciQuadratic_continuousOn D
    (m64AnnulusWithinColumn_continuousOn hf i)
  apply ((((hc 0).const_mul r).add ((hc 1).const_mul r⁻¹)).integrableOn_compact
    m64AnnulusDomain_isCompact).congr
  rw [m64Annulus_restrict_closed_eq_interior]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  simp only [Pi.add_apply, m64AnnulusWithinColumn,
    mfderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)]

end PoincareConjecture
