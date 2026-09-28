import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.Right
import Mathlib.Analysis.Calculus.FDeriv.WithLp













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_exists_two_arc_corner_chart
    {α β : ℝ → AnnulusCoordinates} {Jα Jβ : Set ℝ}
    (hJα : IsOpen Jα) (hJβ : IsOpen Jβ) (h0α : 0 ∈ Jα) (h0β : 0 ∈ Jβ)
    (hα : ContDiffOn ℝ ∞ α Jα) (hβ : ContDiffOn ℝ ∞ β Jβ)
    (hbase : β 0 = α 0)
    (hind : LinearIndependent ℝ (![deriv α 0, deriv β 0] : Fin 2 → AnnulusCoordinates)) :
    ∃ H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (0 : AnnulusCoordinates) ∈ H.source ∧ H 0 = α 0 ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm H.target ∧
      (∀ s : ℝ, H !₂[s, 0] = α s) ∧ (∀ s : ℝ, H !₂[0, s] = β s) ∧
      mfderiv (𝓡 2) (𝓡 2) H 0 !₂[1, 0] = deriv α 0 ∧
      mfderiv (𝓡 2) (𝓡 2) H 0 !₂[0, 1] = deriv β 0 := by
  let e (z : AnnulusCoordinates) := α (z 0) + β (z 1) - α 0
  let U : Set AnnulusCoordinates := {z | z 0 ∈ Jα ∧ z 1 ∈ Jβ}
  have hU : IsOpen U :=
    (hJα.preimage (by fun_prop : Continuous fun z : AnnulusCoordinates => z 0)).inter
      (hJβ.preimage (by fun_prop : Continuous fun z : AnnulusCoordinates => z 1))
  have h0 : (0 : AnnulusCoordinates) ∈ U := ⟨h0α, h0β⟩
  have hproj (i : Fin 2) : ContDiff ℝ ∞ (fun z : AnnulusCoordinates => z i) := by
    fun_prop
  have he : ContDiffOn ℝ ∞ e U :=
    ((hα.comp (hproj 0).contDiffOn (fun _ hz => hz.1)).add
      (hβ.comp (hproj 1).contDiffOn (fun _ hz => hz.2))).sub contDiffOn_const
  let D : AnnulusCoordinates →L[ℝ] AnnulusCoordinates :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).smulRight (deriv α 0) +
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1).smulRight (deriv β 0)
  have hαd := ((hα.contDiffAt (hJα.mem_nhds h0α)).differentiableAt (by simp)).hasDerivAt
  have hβd := ((hβ.contDiffAt (hJβ.mem_nhds h0β)).differentiableAt (by simp)).hasDerivAt
  have hαD : HasFDerivAt (𝕜 := ℝ) (fun z : AnnulusCoordinates => α (z 0))
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).smulRight (deriv α 0))
      (0 : AnnulusCoordinates) := by
    convert! hαd.hasFDerivAt.comp (0 : AnnulusCoordinates)
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (0 : AnnulusCoordinates) 0) using 1
  have hβD : HasFDerivAt (𝕜 := ℝ) (fun z : AnnulusCoordinates => β (z 1))
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1).smulRight (deriv β 0))
      (0 : AnnulusCoordinates) := by
    convert! hβd.hasFDerivAt.comp (0 : AnnulusCoordinates)
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (0 : AnnulusCoordinates) 1) using 1
  have heD : HasFDerivAt e D 0 := by
    exact (hαD.add hβD).sub_const (α 0)
  have hDinj : Function.Injective D := by
    intro z w hzw
    have heq : (fun i : Fin 2 => z i) = (fun i : Fin 2 => w i) :=
      hind.fintypeLinearCombination_injective (by
        simpa [D, Fintype.linearCombination_apply, Fin.sum_univ_two] using hzw)
    ext i
    exact congrFun heq i
  have hei : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e 0) := by
    rw [mfderiv_eq_fderiv, heD.fderiv]
    exact hDinj
  obtain ⟨H, hH0, _, hHe, hH, hHi⟩ := m64Intrinsic_exists_smooth_polar_inverse
    hU (contMDiffOn_iff_contDiffOn.mpr he) h0 hei
  refine ⟨H, hH0, ?_, contMDiffOn_iff_contDiffOn.mpr hH,
    contMDiffOn_iff_contDiffOn.mpr hHi, ?_, ?_, ?_, ?_⟩
  · rw [hHe]
    simp [e, hbase]
  · intro s
    rw [hHe]
    simp [e, hbase]
  · intro s
    rw [hHe]
    change α 0 + β s - α 0 = β s
    abel
  · rw [hHe, mfderiv_eq_fderiv, heD.fderiv]
    change (1 : ℝ) • deriv α 0 + (0 : ℝ) • deriv β 0 = deriv α 0
    simp
  · rw [hHe, mfderiv_eq_fderiv, heD.fderiv]
    change (0 : ℝ) • deriv α 0 + (1 : ℝ) • deriv β 0 = deriv β 0
    simp

end PoincareConjecture
