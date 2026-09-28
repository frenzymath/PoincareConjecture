import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMotionTangent

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {k : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin k)) N] [IsManifold (𝓡 k) ∞ N]
  {a b : ℝ}

def m64AmbientMotionEnergy (F : RicciFlow k N (Icc a b))
    (time : ℝ) (Phi : ℝ × M → N) (w : ℝ × TangentBundle (𝓡 n) M) : ℝ :=
  (1 / 2 : ℝ) * (F.metric (time + w.1)).inner (Phi (w.1, w.2.proj))
    (m64AmbientMotionTangent (n := n) Phi w).snd
    (m64AmbientMotionTangent (n := n) Phi w).snd

theorem m64AmbientMotionEnergy_contMDiffOn (F : RicciFlow k N (Icc a b))
    (time : ℝ) {T : Set ℝ} (hT : IsOpen T) {O : Set M} (hO : IsOpen O)
    (hTF : ∀ s ∈ T, time + s ∈ Ioo a b) (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi (T ×ˢ O)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) 𝓘(ℝ, ℝ) ∞
      (m64AmbientMotionEnergy F time Phi)
      (T ×ˢ {v : TangentBundle (𝓡 n) M | v.proj ∈ O}) := by
  intro w hw
  have hV : IsOpen {v : TangentBundle (𝓡 n) M | v.proj ∈ O} :=
    hO.preimage (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)))
  have hcol := (m64AmbientMotionTangent_contMDiffOn hT hO Phi hPhi).contMDiffAt
    ((hT.prod hV).mem_nhds hw)
  have hbase := (Bundle.contMDiffAt_proj (TangentSpace (𝓡 k))).comp w hcol
  have hm := (F.smooth.contMDiffAt
    (prod_mem_nhds (Icc_mem_nhds (hTF w.1 hw.1).1 (hTF w.1 hw.1).2) univ_mem)).comp w
      ((contMDiffAt_const.add contMDiffAt_fst).prodMk hbase)
  have hp := hm.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial N ℝ) hcol hcol
  have hh := (Bundle.contMDiffAt_totalSpace.mp hp).2
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply] at hh
  exact (contMDiffAt_const.mul hh).contMDiffWithinAt

theorem m64TangentScalar_timePartial_continuousOn {T : Set ℝ} (hT : IsOpen T)
    {V : Set (TangentBundle (𝓡 n) M)} (hV : IsOpen V)
    (H : ℝ × TangentBundle (𝓡 n) M → ℝ)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) 𝓘(ℝ, ℝ) 1 H (T ×ˢ V)) :
    ContinuousOn (fun w : ℝ × TangentBundle (𝓡 n) M => deriv (fun s => H (s, w.2)) w.1)
      (T ×ˢ V) := by
  intro w hw
  have hp : ContMDiffAt
      (((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 1
      (Function.uncurry (fun p : ℝ × TangentBundle (𝓡 n) M => fun s => H (s, p.2)))
      (w, w.1) :=
    (hH.contMDiffAt ((hT.prod hV).mem_nhds hw)).comp (w, w.1)
      (contMDiffAt_snd.prodMk contMDiffAt_fst.snd)
  have hd := hp.mfderiv (fun p : ℝ × TangentBundle (𝓡 n) M => fun s => H (s, p.2))
    Prod.fst (m := 0) contMDiffAt_fst (by norm_num)
  have hh := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
  have hresult : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) 𝓘(ℝ, ℝ) 0
      (fun p : ℝ × TangentBundle (𝓡 n) M => deriv (fun s => H (s, p.2)) p.1) w := by
    simpa +instances only [inTangentCoordinates_model_space, mfderiv_eq_fderiv,
      fderiv_apply_one_eq_deriv] using! hh
  exact hresult.continuousAt.continuousWithinAt

end PoincareConjecture
