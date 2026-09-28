import PoincareConjecture.Proofs.M36.CylinderModelField
import PoincareConjecture.Proofs.M36.RetainedDifferential










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem sphere_chart_target_univ (theta : UnitTwoSphere) :
    (chartAt E₂ theta).target = Set.univ := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  change (stereographic' 2 (-theta)).target = Set.univ
  simp

theorem sphere_chart_inverse_contMDiff (theta : UnitTwoSphere) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (chartAt E₂ theta).symm := by
  intro p
  apply contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas theta)
  rw [sphere_chart_target_univ]
  exact Set.mem_univ p

noncomputable def centeredCylinderLift (theta : UnitTwoSphere) (s : ℝ) (p : E₃) :
    RoundCylinderSpace :=
  ((chartAt E₂ theta).symm (cylinderHorizontalProjection p), cylinderHeightCovector p + s)

theorem centeredCylinderLift_contMDiff (theta : UnitTwoSphere) (s : ℝ) :
    ContMDiff (𝓡 3) IC ∞ (centeredCylinderLift theta s) :=
  ((sphere_chart_inverse_contMDiff theta).comp
    cylinderHorizontalProjection.contDiff.contMDiff).prodMk
      (cylinderHeightCovector.contDiff.contMDiff.add contMDiff_const)

theorem centeredCylinderLift_zero (theta : UnitTwoSphere) (s : ℝ) :
    centeredCylinderLift theta s 0 = (theta, s) := by
  simp only [centeredCylinderLift, map_zero, zero_add]
  congr 1
  rw [← sphere_chart_center_zero theta]
  exact (chartAt E₂ theta).left_inv (mem_chart_source E₂ theta)

theorem centeredCylinderLift_mfderiv (theta : UnitTwoSphere) (s : ℝ) (p v : E₃) :
    mfderiv (𝓡 3) IC (centeredCylinderLift theta s) p v =
      (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm
        (cylinderHorizontalProjection p) (cylinderHorizontalProjection v),
        cylinderHeightCovector v) := by
  have hc := (sphere_chart_inverse_contMDiff theta).mdifferentiable (by simp)
  have hP := (cylinderHorizontalProjection.contDiff (n := ∞)).contMDiff.mdifferentiable
    (by simp)
  have hd := ((cylinderHeightCovector.contDiff (n := ∞)).contMDiff.add
    (contMDiff_const (c := s))).mdifferentiable (by simp)
  have hPd : mfderiv (𝓡 3) (𝓡 2) cylinderHorizontalProjection p =
      cylinderHorizontalProjection := by
    rw [mfderiv_eq_fderiv, cylinderHorizontalProjection.fderiv]
  have hdd : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun q => cylinderHeightCovector q + s) p =
      cylinderHeightCovector := by
    rw [mfderiv_eq_fderiv]
    exact (cylinderHeightCovector.hasFDerivAt.add_const s).fderiv
  have hderiv := mfderiv_prodMk ((hc _).comp p (hP p)) (hd p)
  rw [mfderiv_comp p (hc _) (hP p), hPd] at hderiv
  change mfderiv (𝓡 3) IC (centeredCylinderLift theta s) p =
    (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm (cylinderHorizontalProjection p) |>.comp
      cylinderHorizontalProjection).prod
        (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun q => cylinderHeightCovector q + s) p) at hderiv
  rw [hdd] at hderiv
  exact congrArg (fun D => D v) hderiv

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

def centeredNeckDomain (N : EpsilonNeck g) (s : ℝ) : Set E₃ :=
  {q | cylinderHeightCovector q + s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}

theorem centeredNeckDomain_isOpen (N : EpsilonNeck g) (s : ℝ) :
    IsOpen (centeredNeckDomain N s) :=
  isOpen_Ioo.preimage (cylinderHeightCovector.continuous.add continuous_const)

theorem zero_mem_centeredNeckDomain (N : EpsilonNeck g) {s : ℝ}
    (hs : s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) : 0 ∈ centeredNeckDomain N s := by
  simpa only [centeredNeckDomain, Set.mem_ofPred_eq, map_zero, zero_add] using hs

noncomputable def centeredNeckLift (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ) :
    E₃ → M := N.coordinate_map ∘ centeredCylinderLift theta s

theorem centeredNeckLift_mem (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ)
    {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    centeredNeckLift N theta s p ∈ N.carrier :=
  neck_coordinate_mem N (centeredCylinderLift theta s p) ⟨Set.mem_univ _, hp⟩

theorem centeredNeckLift_contMDiffAt (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ)
    {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (centeredNeckLift N theta s) p :=
  (neck_coordinate_contMDiffAt N (z := centeredCylinderLift theta s p)
    ⟨Set.mem_univ _, hp⟩).comp p
    (centeredCylinderLift_contMDiff theta s p)

theorem centeredNeckLift_zero (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ) :
    centeredNeckLift N theta s 0 = N.coordinate_map (theta, s) := by
  simp only [centeredNeckLift, Function.comp_apply, centeredCylinderLift_zero]

noncomputable def centeredNeckInverse (N : EpsilonNeck g) (theta : UnitTwoSphere)
    (s : ℝ) (x : M) : E₃ :=
  cylinderEuclideanEquiv.symm
    ((chartAt E₂ theta) (N.coordinate_inverse x).1, (N.coordinate_inverse x).2 - s)

theorem centeredNeckInverse_lift (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ)
    {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    centeredNeckInverse N theta s (centeredNeckLift N theta s p) = p := by
  have htarget : cylinderHorizontalProjection p ∈ (chartAt E₂ theta).target := by
    rw [sphere_chart_target_univ]
    exact Set.mem_univ _
  unfold centeredNeckInverse centeredNeckLift
  rw [Function.comp_apply, neck_inverse_coordinate N (centeredCylinderLift theta s p)
    ⟨Set.mem_univ _, hp⟩]
  simp only [centeredCylinderLift, (chartAt E₂ theta).right_inv htarget,
    add_sub_cancel_right]
  change cylinderEuclideanEquiv.symm (cylinderEuclideanEquiv p) = p
  exact cylinderEuclideanEquiv.symm_apply_apply p

theorem centeredNeckInverse_contMDiffAt_lift (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (centeredNeckInverse N theta s)
      (centeredNeckLift N theta s p) := by
  have hN := neck_inverse_contMDiffAt N (centeredNeckLift_mem N theta s hp)
  have hsource : (N.coordinate_inverse (centeredNeckLift N theta s p)).1 ∈
      (chartAt E₂ theta).source := by
    rw [centeredNeckLift, Function.comp_apply,
      neck_inverse_coordinate N (centeredCylinderLift theta s p) ⟨Set.mem_univ _, hp⟩]
    exact (chartAt E₂ theta).map_target (by rw [sphere_chart_target_univ]; exact Set.mem_univ _)
  have hc := contMDiffAt_of_mem_maximalAtlas (I := 𝓡 2) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas theta) hsource
  have hfirst : ContMDiffAt (𝓡 3) (𝓡 2) ∞
      (fun x : M => (chartAt E₂ theta) (N.coordinate_inverse x).1)
      (centeredNeckLift N theta s p) :=
    hc.comp (centeredNeckLift N theta s p) hN.fst
  have hsecond : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : M => (N.coordinate_inverse x).2 - s)
      (centeredNeckLift N theta s p) := hN.snd.sub contMDiffAt_const
  exact cylinderEuclideanEquiv.symm.contDiff.contMDiff.contMDiffAt.comp _
    ((contMDiffAt_prod_module_iff _).mpr ⟨hfirst, hsecond⟩)

theorem centeredNeckLift_mfderiv_isInvertible (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p).IsInvertible := by
  have he := (centeredNeckLift_contMDiffAt N theta s hp).mdifferentiableAt (by simp)
  have hk := (centeredNeckInverse_contMDiffAt_lift N theta s hp).mdifferentiableAt (by simp)
  have hlocal : centeredNeckInverse N theta s ∘ centeredNeckLift N theta s =ᶠ[𝓝 p] id := by
    filter_upwards [(centeredNeckDomain_isOpen N s).mem_nhds hp] with q hq
    exact centeredNeckInverse_lift N theta s hq
  have hinj := mfderiv_injective_of_local_leftInverse he hk hlocal
  let D : E₃ →L[ℝ] E₃ := mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p
  have hbij : Function.Bijective D := ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := D.toLinearMap) rfl).mp hinj⟩
  exact ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2), rfl⟩

end PoincareConjecture.M36
