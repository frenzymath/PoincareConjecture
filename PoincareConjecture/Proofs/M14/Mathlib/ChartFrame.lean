import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace VectorField

noncomputable def chartFrame (x : M) (v : E) (y : M) : TangentSpace I y :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ y v

theorem chartFrame_contMDiffOn (x : M) (v : E) :
    ContMDiffOn I I.tangent ∞ (T% (chartFrame I x v)) (chartAt H x).source := by
  let e := trivializationAt E (TangentSpace I) x
  have hmap : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (y, v)) e.baseSet := contMDiffOn_id.prodMk contMDiffOn_const
  apply (e.contMDiffOn_symm.comp hmap (fun y hy => e.mem_target.mpr hy)).congr
  intro y hy
  rw [show chartFrame I x v y = e.symm y v from Trivialization.symmL_apply e hy v]
  exact e.mk_symm hy v

theorem chartFrame_eq_mpullback {x y : M} (hy : y ∈ (chartAt H x).source) (v : E) :
    chartFrame I x v y = mpullback I 𝓘(ℝ, E) (extChartAt I x) (fun _ => v) y := by
  symm
  have hy' : y ∈ (extChartAt I x).source := by simpa only [extChartAt_source] using hy
  apply (isInvertible_mfderiv_extChartAt (I := I) hy').inverse_apply_eq.mpr
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy]
  exact ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt_symmL
    (R := ℝ) hy v).symm

variable [CompleteSpace E]

theorem chartFrame_mlieBracket {x y : M} (hy : y ∈ (chartAt H x).source) (v w : E) :
    mlieBracket I (chartFrame I x v) (chartFrame I x w) y = 0 := by
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  let : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le htwo
  have heq (z : E) : chartFrame I x z =ᶠ[𝓝 y]
      mpullback I 𝓘(ℝ, E) (extChartAt I x) (fun _ => z) := by
    filter_upwards [(chartAt H x).open_source.mem_nhds hy] with p hp
    exact chartFrame_eq_mpullback I hp z
  rw [(heq v).mlieBracket_vectorField_eq (heq w)]
  have hconst (z : E) :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt
      (𝕜 := ℝ) (V := fun _ => z) (x := extChartAt I x y) (n := (1 : ℕ∞ω))).mpr
      contDiffAt_const).mdifferentiableAt one_ne_zero
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I x) y :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) hy
  rw [← mpullback_mlieBracket (hconst v) (hconst w) hchart htwo]
  have hzero : mlieBracket 𝓘(ℝ, E) (fun _ : E => v) (fun _ : E => w) = 0 := by
    funext q
    change mlieBracketWithin 𝓘(ℝ, E) (fun _ => v) (fun _ => w) univ q = 0
    rw [mlieBracketWithin_eq_lieBracketWithin]
    simp [lieBracketWithin]
  rw [hzero, mpullback_zero]
  rfl

omit [CompleteSpace E] in

theorem chartFrame_mfderiv_extChartAt {x y : M} (hy : y ∈ (chartAt H x).source)
    (v : TangentSpace I y) :
    chartFrame I x (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y v) y = v := by
  rw [chartFrame, ← TangentBundle.continuousLinearMapAt_trivializationAt hy]
  exact (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt hy v

omit [CompleteSpace E] in

theorem chartFrame_curve_deriv {γ : ℝ → M} {x : M} {s : ℝ}
    (hx : γ s ∈ (chartAt H x).source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ s) :
    chartFrame I x (deriv ((extChartAt I x) ∘ γ) s) (γ s) =
      mfderiv 𝓘(ℝ) I γ s (1 : ℝ) := by
  have hc := (contMDiffAt_extChartAt' (I := I) (n := ∞) hx).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply s hc hγ (1 : ℝ)
  have hderiv : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ((extChartAt I x) ∘ γ) s (1 : ℝ) =
      deriv ((extChartAt I x) ∘ γ) s := by
    exact (congrArg (fun L : ℝ →L[ℝ] E => L 1)
      (mfderiv_eq_fderiv (f := (extChartAt I x) ∘ γ) (x := s))).trans
        fderiv_apply_one_eq_deriv
  have hd : deriv ((extChartAt I x) ∘ γ) s =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) (γ s) (mfderiv 𝓘(ℝ) I γ s (1 : ℝ)) := by
    exact hderiv.symm.trans h
  rw [hd]
  exact chartFrame_mfderiv_extChartAt I hx _

end VectorField
