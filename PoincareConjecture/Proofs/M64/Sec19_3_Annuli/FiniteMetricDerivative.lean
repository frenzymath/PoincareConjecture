import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteParameterJets
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMovingMetricDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m64ParameterAnnulus_moving_metric_energy_hasDerivAt
    (F : RicciFlow n M (Icc a b)) (r : ℝ) {t : ℝ} (ht : t ∈ Ioo a b)
    {Phi : ℝ × E → M} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hPhi : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ Phi O)
    {h : LoopPlane → E} {p : LoopPlane} (hh : DifferentiableAt ℝ h p)
    (hp : (0, h p) ∈ O) :
    let v := fun s q => Phi (s, h q)
    let d := mfderiv (𝓡 2) (𝓡 n) (v 0) p
    HasDerivAt (fun s => m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p)
      (deriv (fun s => m64ModulusEnergyDensity (F.metric t) r (v s) p) 0 -
        r * (F.connection t).ricci (v 0 p)
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 0)) -
        r⁻¹ * (F.connection t).ricci (v 0 p)
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))) 0 := by
  let H := fun q : LoopPlane => h p + fderiv ℝ h p (q - p)
  have hHp : H p = h p := by simp [H]
  have hH : HasFDerivAt H (fderiv ℝ h p) p := by
    simpa only [H, ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using!
      (((fderiv ℝ h p).hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const p)).const_add (h p))
  have hHs : ContDiff ℝ ∞ H := by dsimp only [H]; fun_prop
  let v := fun s q => Phi (s, h q)
  let w := fun s q => Phi (s, H q)
  have hproxy : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞
      (fun q => w q.1 q.2) (0, p) := by
    have heq : ((0 : ℝ), H p) = (0, h p) := Prod.ext rfl hHp
    exact (heq.symm ▸ hPhi.contMDiffAt (hO.mem_nhds hp)).comp (0, p)
      ((contDiffAt_fst.prodMk (hHs.contDiffAt.comp (0, p) contDiffAt_snd)).contMDiffAt)
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), (s, h p) ∈ O :=
    (continuous_id.prodMk continuous_const).continuousAt (hO.mem_nhds hp)
  have heq (g : RiemannianMetric n M) (s : ℝ) (hs : (s, h p) ∈ O) :
      m64ModulusEnergyDensity g r (v s) p = m64ModulusEnergyDensity g r (w s) p :=
    m64ParameterAnnulus_energy_eq_of_firstJet g r
      ((hPhi.contMDiffAt (hO.mem_nhds hs)).mdifferentiableAt (by simp))
      hh hH.differentiableAt hHp.symm hH.fderiv.symm
  have hfixed : (fun s => m64ModulusEnergyDensity (F.metric t) r (v s) p) =ᶠ[𝓝 0]
      fun s => m64ModulusEnergyDensity (F.metric t) r (w s) p :=
    hnear.mono fun s hs => heq (F.metric t) s hs
  have hmove : (fun s => m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p) =ᶠ[𝓝 0]
      fun s => m64ModulusEnergyDensity (F.metric (t + s)) r (w s) p :=
    hnear.mono fun s hs => heq (F.metric (t + s)) s hs
  have hcol (d : LoopPlane) : mfderiv (𝓡 2) (𝓡 n) (w 0) p d =
      mfderiv (𝓡 2) (𝓡 n) (v 0) p d :=
    (m64ParameterAnnulus_differential_eq_of_firstJet
      ((hPhi.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp))
      hh hH.differentiableAt hHp.symm hH.fderiv.symm d).symm
  have hric (i : Fin 2) :
      (F.connection t).ricci (w 0 p)
        (mfderiv (𝓡 2) (𝓡 n) (w 0) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 n) (w 0) p (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      (F.connection t).ricci (v 0 p)
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
    have hdata : (w 0 p,
        (mfderiv (𝓡 2) (𝓡 n) (w 0) p (EuclideanSpace.basisFun (Fin 2) ℝ i) :
          EuclideanSpace ℝ (Fin n))) =
        (v 0 p,
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ i) :
          EuclideanSpace ℝ (Fin n))) :=
      Prod.ext (congrArg (fun q => Phi (0, q)) hHp) (hcol _)
    exact congrArg (fun q : M × EuclideanSpace ℝ (Fin n) =>
      (F.connection t).ricci q.1 q.2 q.2) hdata
  have hd := m64ModulusAnnulus_moving_metric_energy_hasDerivAt F r ht p hproxy
  apply (hd.congr_of_eventuallyEq hmove).congr_deriv
  change deriv (fun s => m64ModulusEnergyDensity (F.metric t) r (w s) p) 0 -
    r * (F.connection t).ricci (w 0 p)
      (mfderiv (𝓡 2) (𝓡 n) (w 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (mfderiv (𝓡 2) (𝓡 n) (w 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) -
    r⁻¹ * (F.connection t).ricci (w 0 p)
      (mfderiv (𝓡 2) (𝓡 n) (w 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
      (mfderiv (𝓡 2) (𝓡 n) (w 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = _
  rw [hric 0, hric 1, ← hfixed.deriv_eq]

end PoincareConjecture
