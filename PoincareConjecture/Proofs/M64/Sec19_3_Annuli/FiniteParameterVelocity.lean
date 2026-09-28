import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingCurveEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.PullbackParameterFirstJet





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem m64ParameterMotion_timeVelocity_contMDiffAt
    {Phi : ℝ × E → M} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hPhi : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ Phi O)
    {q : ℝ × E} (hq : q ∈ O) :
    ContMDiffAt 𝓘(ℝ, ℝ × E) ((𝓡 n).prod (𝓡 n)) ∞
      (fun w : ℝ × E => (⟨Phi w, curveVelocity (fun s => Phi (s, w.2)) w.1⟩ :
        TangentBundle (𝓡 n) M)) q := by
  have hqreg := hPhi.contMDiffAt (hO.mem_nhds hq)
  have hvec : ContMDiffAt 𝓘(ℝ, ℝ × E)
      ((𝓘(ℝ, ℝ × E)).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun w : ℝ × E => (⟨w, (1, 0)⟩ : TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × E))) q := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := ((1 : ℝ), (0 : E)))⟩
  have hpush := (hqreg.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
    hvec hqreg
  apply hpush.congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hq] with w hw
  have hline := hasFDerivAt_prodMk_left (𝕜 := ℝ) w.1 w.2
  have hchain := mfderiv_comp_apply w.1
    ((hPhi.contMDiffAt (hO.mem_nhds hw)).mdifferentiableAt (by simp))
    hline.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [mfderiv_eq_fderiv, hline.fderiv] at hchain
  exact congrArg (fun v : TangentSpace (𝓡 n) (Phi w) =>
    (⟨Phi w, v⟩ : TangentBundle (𝓡 n) M)) hchain

omit [IsManifold (𝓡 n) ∞ M] in




theorem m64ParameterMotion_spatial_velocity
    {Phi : ℝ × E → M} {h : ℝ → E} {t x : ℝ}
    (hPhi : MDifferentiableAt 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (t, h x))
    (hh : DifferentiableAt ℝ h x) :
    curveVelocity (n := n) (fun y => Phi (t, h y)) x =
      mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (t, h x) (0, deriv h x) := by
  have harg := (hasDerivAt_const x t).prodMk hh.hasDerivAt
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × E) (fun y => (t, h y)) x 1 =
      (0, deriv h x) := by
    rw [mfderiv_eq_fderiv, harg.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hc := mfderiv_comp_apply x hPhi harg.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hd] at hc
  exact hc

end PoincareConjecture
