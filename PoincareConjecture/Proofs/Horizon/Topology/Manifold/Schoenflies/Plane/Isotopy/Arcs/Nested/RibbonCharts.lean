import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

theorem exists_chart_of_ribbon_edge
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (c : Real)
    {a w : Real} (ha : 0 < a) (haw : a < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, c]) ∈ A '' sphere (0 : E2) 1) :
    ∃ e : OpenPartialHomeomorph E1 S1,
      closedBall (0 : E1) a ⊆ e.source ∧
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e e.source ∧
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e.symm e.target ∧
      ∀ x ∈ closedBall (0 : E1) a,
        A (e x) = R (WithLp.toLp 2 ![x 0, c]) := by
  let G : E1 → E2 := fun x => A.symm (R (WithLp.toLp 2 ![x 0, c]))
  let H : E2 → E1 := fun y => WithLp.toLp 2 ![(R.symm (A y)) 0]
  have hG : ContDiff Real ∞ G := by
    apply A.symm.contMDiff.contDiff.comp
    apply R.contMDiff.contDiff.comp
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 1)).contDiff
    · exact contDiff_const
  have hH : ContDiff Real ∞ H := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp
      (R.symm.contMDiff.contDiff.comp A.contMDiff.contDiff)
  have hHG : H ∘ G = id := by
    funext x
    ext i
    fin_cases i
    simp [H, G]
  have hGi : Injective G := by
    intro x y hxy
    have h := congrArg H hxy
    exact (congrFun hHG x).symm.trans (h.trans (congrFun hHG y))
  have hGder (x : E1) : Injective (fderiv Real G x) := by
    have hc := fderiv_comp x (hH.differentiable (by simp) (G x))
      (hG.differentiable (by simp) x)
    rw [hHG, fderiv_id] at hc
    intro u v huv
    have hh := congrArg (fderiv Real H (G x)) huv
    change ((fderiv Real H (G x)).comp (fderiv Real G x)) u =
      ((fderiv Real H (G x)).comp (fderiv Real G x)) v at hh
    simpa only [← hc, ContinuousLinearMap.id_apply] using hh
  have hmem (x : E1) (hx : x ∈ closedBall (0 : E1) a) :
      G x ∈ sphere (0 : E2) 1 := by
    have hnorm : ‖x‖ ≤ a := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hx0 : |x 0| ≤ a := (PiLp.norm_apply_le x 0).trans hnorm
    have he := hedge (x 0) ⟨by linarith [(abs_le.mp hx0).1],
      by linarith [(abs_le.mp hx0).2]⟩
    rcases he with ⟨y, hy, he⟩
    change A.symm (R (WithLp.toLp 2 ![x 0, c])) ∈ _
    rw [← he, A.symm_apply_apply]
    exact hy
  let p0 : S1 := ⟨G 0, hmem 0 (mem_closedBall_self ha.le)⟩
  let m : E1 → S1 := Plane.unitRadialProjection p0 ∘ G
  let N : E1 → E2 := fun x => m x
  let U : Set E1 := G ⁻¹' ({0} : Set E2)ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage hG.continuous
  have hballU : closedBall (0 : E1) a ⊆ U := by
    intro x hx
    exact ne_zero_of_mem_unit_sphere ⟨G x, hmem x hx⟩
  have hm : ContMDiffOn (𝓡 1) (𝓡 1) ∞ m U :=
    (Plane.contMDiffOn_unitRadialProjection (n := 1) (m := ∞) p0).comp
      hG.contMDiff.contMDiffOn (fun _ hx => hx)
  have hN : ContDiffOn Real ∞ N U :=
    (contMDiff_coe_sphere.comp_contMDiffOn hm).contDiffOn
  have heq : EqOn N G (closedBall (0 : E1) a) := by
    intro x hx
    exact congrArg Subtype.val
      (Plane.unitRadialProjection_apply_coe p0 ⟨G x, hmem x hx⟩)
  have hUD : UniqueDiffOn Real (closedBall (0 : E1) a) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E1) a) (by
      rw [interior_closedBall (0 : E1) ha.ne']
      exact ⟨0, mem_ball_self ha⟩)
  have hder (x : E1) (hx : x ∈ closedBall (0 : E1) a) :
      fderiv Real N x = fderiv Real G x := by
    rw [← fderivWithin_eq_fderiv (hUD x hx)
      ((hN.contDiffAt (hU.mem_nhds (hballU hx))).differentiableAt (by simp)),
      ← fderivWithin_eq_fderiv (hUD x hx) (hG.differentiable (by simp) x)]
    exact fderivWithin_congr' heq hx
  let V : Set E1 := U ∩ {x | Injective (fderiv Real N x)}
  have hV : IsOpen V :=
    (hN.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage
      hU ContinuousLinearMap.isOpen_injective
  have hballV : closedBall (0 : E1) a ⊆ V := by
    intro x hx
    refine ⟨hballU hx, ?_⟩
    change Injective (fderiv Real N x)
    rw [hder x hx]
    exact hGder x
  have hbij (x : E1) (hx : x ∈ V) : Bijective (mfderiv (𝓡 1) (𝓡 1) m x) := by
    have hmx := hm.contMDiffAt (hU.mem_nhds hx.1)
    have hchain := mfderiv_comp x
      ((contMDiff_coe_sphere (n := 1) (m := ∞) (m x)).mdifferentiableAt (by simp))
      (hmx.mdifferentiableAt (by simp))
    have hinj : Injective (mfderiv (𝓡 1) (𝓡 1) m x) := by
      intro u v huv
      apply hx.2
      have hder' : fderiv Real N x =
          (mfderiv (𝓡 1) (𝓡 2) (fun p : S1 => (p : E2)) (m x)).comp
            (mfderiv (𝓡 1) (𝓡 1) m x) := by
        rw [← mfderiv_eq_fderiv]
        exact hchain
      rw [hder']
      exact congrArg (mfderiv (𝓡 1) (𝓡 2) (fun p : S1 => (p : E2)) (m x)) huv
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E1) (V₂ := E1)
      (f := (mfderiv (𝓡 1) (𝓡 1) m x).toLinearMap) rfl).mp hinj⟩
  have hlocal := Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv
    hV (hm.mono inter_subset_left) hbij
  have hmi : InjOn m (closedBall (0 : E1) a) := by
    intro x hx y hy hxy
    apply hGi
    rw [← heq hx, ← heq hy]
    exact congrArg Subtype.val hxy
  obtain ⟨e, he, _, hem, hes, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact (isCompact_closedBall 0 a)
      hmi (fun x hx => hlocal ⟨x, hballV hx⟩)
  refine ⟨e, he, hes, hei, ?_⟩
  intro x hx
  rw [hem (he hx)]
  change A (N x) = _
  rw [heq hx]
  exact A.apply_symm_apply _

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
