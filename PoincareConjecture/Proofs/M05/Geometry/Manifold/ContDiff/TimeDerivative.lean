
import PoincareConjecture.Proofs.M05.Analysis.Calculus.MixedDerivatives
import PoincareConjecture.Proofs.M05.Geometry.Manifold.VectorField.Derivation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Filter

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [I.Boundaryless] in

lemma contMDiffAt_deriv_time
    {f : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun s => f (s, p.2)) p.1) (t, x) := by
  have hc : ContMDiffAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × M) × ℝ => f (p.2, p.1.2)) ((t, x), t) :=
    hf.comp_of_eq (contMDiffAt_snd.prodMk
      (contMDiffAt_snd.comp ((t, x), t) contMDiffAt_fst)) rfl
  have hd := hc.mfderiv (fun p s => f (s, p.2)) Prod.fst
    contMDiffAt_fst (m := ∞) (by simp)
  have h := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
  convert h using 1
  funext p
  rw [inTangentCoordinates_model_space]
  simp only [mfderiv_eq_fderiv, deriv]


lemma hasDerivAt_mvfderiv_time
    {f : ℝ × M → ℝ} {df : M → ℝ} {t : ℝ} {x : M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (hdf : ∀ y, HasDerivAt (fun s => f (s, y)) (df y) t) (v : TangentSpace I x) :
    HasDerivAt (fun s => mvfderiv I (fun y => f (s, y)) x v)
      (mvfderiv I df x v) t := by
  have hdfx : MDifferentiableAt I 𝓘(ℝ, ℝ) df x := by
    have h := (contMDiffAt_deriv_time hf).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
    have he : (fun y => deriv (fun s => f (s, y)) t) = df :=
      funext fun y => (hdf y).deriv
    change ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => deriv (fun s => f (s, y)) t) x at h
    rw [he] at h
    exact h.mdifferentiableAt (by simp)
  let e := extChartAt I x
  have hx : e.symm (e x) = x := e.left_inv (mem_extChartAt_source x)
  have hs : ContMDiffAt 𝓘(ℝ, E) I ∞ e.symm (e x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hc : ContDiffAt ℝ ∞ (fun p : ℝ × E => f (p.1, e.symm p.2)) (t, e x) := by
    have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × E => (p.1, e.symm p.2)) (t, e x) :=
      contMDiffAt_fst.prodMk (hs.comp (t, e x) contMDiffAt_snd)
    have h := hf.comp_of_eq hp (by simp [hx])
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt
  let w : E := (mfderiv 𝓘(ℝ, E) I e.symm (e x)).inverse v
  have hi := VectorField.isInvertible_mfderiv_extChartAt_symm
    (I := I) (p := x) (mem_extChartAt_target x)
  have h := Analysis.hasDerivAt_fderiv_time hc (fun z => hdf (e.symm z)) w
  have hd : fderiv ℝ (df ∘ e.symm) (e x) w = mvfderiv I df x v := by
    have h := VectorField.fderiv_comp_extChartAt_symm
      (I := I) (f := df) (p := x) (by simpa only [e] using (hx.symm ▸ hdfx))
      (mem_extChartAt_target x) w
    change fderiv ℝ (df ∘ e.symm) (e x) w =
      mfderiv I 𝓘(ℝ, ℝ) df (e.symm (e x)) (mfderiv 𝓘(ℝ, E) I e.symm (e x) w) at h
    dsimp only [w] at h
    rw [hi.self_apply_inverse, hx] at h
    exact h
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  have hevent : ∀ᶠ s in 𝓝 t, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f (s, y)) x := by
    have hnear := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp
      (hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)))
    have htime : Tendsto (fun s : ℝ => (s, x)) (𝓝 t) (𝓝 (t, x)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [htime.eventually hnear] with s hs
    exact (hs.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  filter_upwards [hevent] with s hs
  have h := VectorField.fderiv_comp_extChartAt_symm
    (I := I) (f := fun y => f (s, y)) (p := x) (by simpa only [e] using (hx.symm ▸ hs))
    (mem_extChartAt_target x) w
  change fderiv ℝ ((fun y => f (s, y)) ∘ e.symm) (e x) w =
    mfderiv I 𝓘(ℝ, ℝ) (fun y => f (s, y)) (e.symm (e x))
      (mfderiv 𝓘(ℝ, E) I e.symm (e x) w) at h
  dsimp only [w] at h
  rw [hi.self_apply_inverse, hx] at h
  exact h.symm

end Poincare.Manifold
