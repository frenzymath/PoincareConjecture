import PoincareConjecture.Proofs.M49.RoundCylinderGram
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M49

theorem roundCylinderGram_eq_zero_line (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) :
    roundCylinderGram u c p = roundCylinderGram u c (p.1, 0) := rfl

set_option backward.isDefEq.respectTransparency false in

theorem continuousAt_roundCylinderGram (u : ℝ) (q : UnitTwoSphere)
    {p : RoundCylinderCoordinates}
    (hp : p.1 ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target) :
    ContinuousAt (fun x => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x) p := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
    fun x => (c.symm x).1
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun x : UnitTwoSphere => x.1) :=
    contMDiff_coe_sphere
  have hc : ContMDiffOn (𝓡 2) (𝓡 2) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hF : ContDiffOn ℝ ∞ F c.target :=
    (hs.comp_contMDiffOn hc).contDiffOn
  have hDF : ContinuousAt (fderiv ℝ F) p.1 :=
    ((hF p.1 hp).contDiffAt (c.open_target.mem_nhds hp)).continuousAt_fderiv
      (by simp)
  have hchain (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ c.target) :
      fderiv ℝ F x =
        (mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) (c.symm x)).comp
          (mfderiv (𝓡 2) (𝓡 2) c.symm x) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp x (hs.mdifferentiable (by simp) (c.symm x))
      ((hc.contMDiffAt (c.open_target.mem_nhds hx)).mdifferentiableAt (by simp))
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro j
  have hlocal : ∀ᶠ x : RoundCylinderCoordinates in 𝓝 p, x.1 ∈ c.target :=
    continuousAt_fst (c.open_target.mem_nhds hp)
  have hentry : (fun x : RoundCylinderCoordinates => roundCylinderGram u c x i j) =ᶠ[𝓝 p]
      (fun x => 2 * (1 - u) * inner ℝ
        (fderiv ℝ F x.1 (roundCylinderCoordinateBasis i).1)
        (fderiv ℝ F x.1 (roundCylinderCoordinateBasis j).1) +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2) := by
    filter_upwards [hlocal] with x hx
    rw [hchain x.1 hx]
    rfl
  apply ContinuousAt.congr_of_eventuallyEq _ hentry
  exact (continuousAt_const.mul
    (((hDF.comp continuousAt_fst).clm_apply continuousAt_const).inner
      ((hDF.comp continuousAt_fst).clm_apply continuousAt_const))).add continuousAt_const

end PoincareConjecture.M49
