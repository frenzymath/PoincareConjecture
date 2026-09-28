import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SharedBoundaryTangency
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldPatchChart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_north_boundary_patch_pullback
    (A N : BallNeighborhoodChart E3 E3) (o : ℝ)
    (ho : 0 < o) (ho1 : o < 1)
    (hpatch : ∀ q : UnitTwoSphere, -o < (heightCoordinates (q : E3)).2 →
      N.chart (q : E3) ∈ A.boundary) :
    let R := Real.sqrt ((1 + o) / (1 - o))
    ∃ e : OpenPartialHomeomorph E2 UnitTwoSphere,
      1 < R ∧ e.source = ball (0 : E2) R ∧
      e.target = {q : UnitTwoSphere | ∃ X ∈ ball (0 : E2) R,
        A.chart (q : E3) = N.chart (northSpherePoint X : E3)} ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target ∧
      closedBall (0 : E2) 1 ⊆ e.source ∧
      (∀ X ∈ e.source, (e X : E3) =
        A.chart.symm (N.chart (northSpherePoint X : E3))) ∧
      (∀ q ∈ e.target,
        e.symm q =
          (1 + (heightCoordinates (N.chart.symm (A.chart (q : E3)))).2)⁻¹ •
            (heightCoordinates (N.chart.symm (A.chart (q : E3)))).1) ∧
      A.chart '' (((↑) : UnitTwoSphere → E3) '' (e '' closedBall (0 : E2) 1)) =
        N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let R : ℝ := Real.sqrt ((1 + o) / (1 - o))
  let U : Set E2 := ball (0 : E2) R
  have hden : 0 < 1 - o := sub_pos.mpr ho1
  have hrat : 1 < (1 + o) / (1 - o) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  have hRnonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = (1 + o) / (1 - o) :=
    Real.sq_sqrt (by linarith)
  have hR : 1 < R := by nlinarith
  have hU : IsOpen U := isOpen_ball
  have hclosed : closedBall (0 : E2) 1 ⊆ U := by
    intro X hX
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hX).trans_lt hR)
  have hband (X : E2) (hX : X ∈ U) :
      -o < (heightCoordinates (northSpherePoint X : E3)).2 := by
    have hx : ‖X‖ < R := mem_ball_zero_iff.mp hX
    have hxs : ‖X‖ ^ 2 < (1 + o) / (1 - o) := by
      rw [← hRsq]
      nlinarith [norm_nonneg X]
    have hcross := (lt_div_iff₀ hden).mp hxs
    rw [northSpherePoint_coordinates]
    change -o < (1 - ‖X‖ ^ 2) / (1 + ‖X‖ ^ 2)
    apply (lt_div_iff₀ (by positivity : 0 < 1 + ‖X‖ ^ 2)).mpr
    nlinarith
  have hAs (q : UnitTwoSphere) : (q : E3) ∈ A.chart.source :=
    A.closedBall_subset_source (sphere_subset_closedBall q.property)
  have hNs (q : UnitTwoSphere) : (q : E3) ∈ N.chart.source :=
    N.closedBall_subset_source (sphere_subset_closedBall q.property)
  have hboundary (X : E2) (hX : X ∈ U) :
      N.chart (northSpherePoint X : E3) ∈ A.boundary :=
    hpatch (northSpherePoint X) (hband X hX)
  have hAtarget (X : E2) (hX : X ∈ U) :
      N.chart (northSpherePoint X : E3) ∈ A.chart.target := by
    obtain ⟨y, hy, heq⟩ := hboundary X hX
    rw [← heq]
    exact A.chart.map_source (A.closedBall_subset_source (sphere_subset_closedBall hy))
  have hNtarget (X : E2) :
      N.chart (northSpherePoint X : E3) ∈ N.chart.target :=
    N.chart.map_source (hNs (northSpherePoint X))
  let f : E2 → UnitTwoSphere := fun X =>
    if hX : X ∈ U then
      ⟨A.chart.symm (N.chart (northSpherePoint X : E3)),
        mem_sphere_zero_iff_norm.mpr (A.norm_symm_of_mem_boundary (hboundary X hX))⟩
    else northSpherePoint 0
  have hfcoe (X : E2) (hX : X ∈ U) :
      (f X : E3) = A.chart.symm (N.chart (northSpherePoint X : E3)) := by
    simp only [f, dif_pos hX]
  have hAf (X : E2) (hX : X ∈ U) :
      A.chart (f X : E3) = N.chart (northSpherePoint X : E3) := by
    rw [hfcoe X hX]
    exact A.chart.right_inv (hAtarget X hX)
  have hNf (X : E2) (hX : X ∈ U) :
      N.chart.symm (A.chart (f X : E3)) = (northSpherePoint X : E3) := by
    rw [hAf X hX]
    exact N.chart.left_inv (hNs (northSpherePoint X))
  let g : UnitTwoSphere → E2 := fun q =>
    (1 + (heightCoordinates (N.chart.symm (A.chart (q : E3)))).2)⁻¹ •
      (heightCoordinates (N.chart.symm (A.chart (q : E3)))).1
  have hgf (X : E2) (hX : X ∈ U) : g (f X) = X := by
    change (1 + (heightCoordinates (N.chart.symm (A.chart (f X : E3)))).2)⁻¹ •
      (heightCoordinates (N.chart.symm (A.chart (f X : E3)))).1 = X
    rw [hNf X hX]
    exact northSphereCoordinate_point X
  have hfi : InjOn f U := by
    intro X hX Y hY hXY
    calc
      X = g (f X) := (hgf X hX).symm
      _ = g (f Y) := congrArg g hXY
      _ = Y := hgf Y hY
  have hnp : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞
      (fun X => (northSpherePoint X : E3)) :=
    contMDiff_coe_sphere.comp northSpherePoint_contMDiff
  have hNparam : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞
      (fun X => N.chart (northSpherePoint X : E3)) := by
    apply contMDiffOn_univ.mp
    exact N.smooth.contMDiffOn.comp hnp.contMDiffOn
      (fun X _ => hNs (northSpherePoint X))
  have hfambient : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞
      (fun X => A.chart.symm (N.chart (northSpherePoint X : E3))) U :=
    A.smooth_symm.contMDiffOn.comp hNparam.contMDiffOn
      (fun X hX => hAtarget X hX)
  have hf : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ f U :=
    contMDiffOn_sphere_of_coe hU f (hfambient.congr hfcoe)
  have hAparam : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
      (fun q : UnitTwoSphere => A.chart (q : E3)) := by
    apply contMDiffOn_univ.mp
    exact A.smooth.contMDiffOn.comp contMDiff_coe_sphere.contMDiffOn
      (fun q _ => hAs q)
  have hgs (X : E2) (hX : X ∈ U) :
      ContMDiffAt (𝓡 2) 𝓘(ℝ, E2) ∞ g (f X) := by
    have hNt : A.chart (f X : E3) ∈ N.chart.target := by
      rw [hAf X hX]
      exact hNtarget X
    have hk : ContMDiffAt (𝓡 2) 𝓘(ℝ, E3) ∞
        (fun q : UnitTwoSphere => N.chart.symm (A.chart (q : E3))) (f X) :=
      (N.smooth_symm.contDiffAt (N.chart.open_target.mem_nhds hNt)).contMDiffAt.comp
        (f X) (hAparam (f X))
    have hC : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2 × ℝ) ∞
        (fun q : UnitTwoSphere =>
          heightCoordinates (N.chart.symm (A.chart (q : E3)))) (f X) :=
      heightCoordinates.contDiff.contMDiff.contMDiffAt.comp (f X) hk
    have hh : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2) ∞
        (fun q : UnitTwoSphere =>
          (heightCoordinates (N.chart.symm (A.chart (q : E3)))).1) (f X) :=
      contDiff_fst.contMDiff.contMDiffAt.comp (f X) hC
    have hd : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : UnitTwoSphere =>
          1 + (heightCoordinates (N.chart.symm (A.chart (q : E3)))).2) (f X) :=
      (contDiff_const.add contDiff_snd).contMDiff.contMDiffAt.comp (f X) hC
    have hn : 1 + (heightCoordinates (N.chart.symm (A.chart (f X : E3)))).2 ≠ 0 := by
      rw [hNf X hX]
      have hm := northSpherePoint_mem_domain X
      change -1 < (heightCoordinates (northSpherePoint X : E3)).2 at hm
      linarith
    exact ((contDiffAt_inv ℝ hn).contMDiffAt.comp (f X) hd).smul hh
  have hfb (X : E2) (hX : X ∈ U) :
      Bijective (mfderiv 𝓘(ℝ, E2) (𝓡 2) f X) := by
    have hfd := (hf.contMDiffAt (hU.mem_nhds hX)).mdifferentiableAt (by simp)
    have hgd := (hgs X hX).mdifferentiableAt (by simp)
    have heq : g ∘ f =ᶠ[𝓝 X] id := by
      filter_upwards [hU.mem_nhds hX] with Y hY
      exact hgf Y hY
    have hd := hgd.hasMFDerivAt.comp X hfd.hasMFDerivAt
    have hcomp := hd.mfderiv
    rw [heq.mfderiv_eq, mfderiv_id] at hcomp
    let L : E2 →L[ℝ] E2 := mfderiv 𝓘(ℝ, E2) (𝓡 2) f X
    let K : E2 →L[ℝ] E2 := mfderiv (𝓡 2) 𝓘(ℝ, E2) g (f X)
    have hKL : ContinuousLinearMap.id ℝ E2 = K.comp L := hcomp
    have hLi : Injective L := by
      intro v w hvw
      have hv := congrArg (fun D : E2 →L[ℝ] E2 => D v) hKL
      have hw := congrArg (fun D : E2 →L[ℝ] E2 => D w) hKL
      change v = K (L v) at hv
      change w = K (L w) at hw
      exact hv.trans ((congrArg K hvw).trans hw.symm)
    have hLs : Surjective L :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := L.toLinearMap) (show Module.finrank ℝ E2 = Module.finrank ℝ E2 from rfl)).mp hLi
    exact ⟨hLi, hLs⟩
  let e := manifoldPatchChart f hU hf hfb hfi
  have hetarget : e.target = {q : UnitTwoSphere | ∃ X ∈ U,
      A.chart (q : E3) = N.chart (northSpherePoint X : E3)} := by
    change f '' U = _
    ext q
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact ⟨X, hX, hAf X hX⟩
    · rintro ⟨X, hX, hq⟩
      refine ⟨X, hX, ?_⟩
      apply Subtype.ext
      apply A.chart.injOn (hAs (f X)) (hAs q)
      exact (hAf X hX).trans hq.symm
  have heinv (q : UnitTwoSphere) (hq : q ∈ e.target) : e.symm q = g q := by
    have hx : e.symm q ∈ U := e.map_target hq
    have hqf : f (e.symm q) = q := e.right_inv hq
    calc
      e.symm q = g (f (e.symm q)) := (hgf (e.symm q) hx).symm
      _ = g q := congrArg g hqf
  have hcap :
      A.chart '' (((↑) : UnitTwoSphere → E3) '' (e '' closedBall (0 : E2) 1)) =
        N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    apply Subset.antisymm
    · rintro _ ⟨y, ⟨q, ⟨X, hX, rfl⟩, rfl⟩, rfl⟩
      change A.chart (f X : E3) ∈ _
      rw [hAf X (hclosed hX)]
      exact ⟨(northSpherePoint X : E3),
        ⟨norm_eq_of_mem_sphere (northSpherePoint X),
          (northSpherePoint_height_nonneg_iff X).mpr (mem_closedBall_zero_iff.mp hX)⟩, rfl⟩
    · rintro _ ⟨y, ⟨hy, hz⟩, rfl⟩
      let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
      have hq : q ∈ northSpherePoint '' closedBall (0 : E2) 1 := by
        rw [northSpherePoint_image_closedBall]
        exact hz
      obtain ⟨X, hX, hXq⟩ := hq
      refine ⟨(e X : E3), ⟨e X, ⟨X, hX, rfl⟩, rfl⟩, ?_⟩
      change A.chart (f X : E3) = N.chart (q : E3)
      rw [hAf X (hclosed hX)]
      exact congrArg (fun p : UnitTwoSphere => N.chart (p : E3)) hXq
  refine ⟨e, hR, rfl, hetarget, hf, ?_, hclosed, ?_, ?_, hcap⟩
  · exact manifoldPatchChart_symm_contMDiffOn f hU hf hfb hfi
  · intro X hX
    exact hfcoe X hX
  · intro q hq
    exact heinv q hq

end PoincareConjecture.M25.Topology3D
