import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallStraightening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.LinearBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Radial












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩



theorem exists_marked_ball_normalization
    (v : EuclideanSpace Real (Fin 3)) (hv : ‖v‖ = 1)
    {r : Real} (hr : 0 < r)
    (f : Hemisphere.Plane v -> sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (hcenter : (f 0 : EuclideanSpace Real (Fin 3)) = v)
    (hinj : InjOn f (closedBall 0 r))
    (hloc : ∀ x ∈ closedBall (0 : Hemisphere.Plane v) r,
      IsLocalDiffeomorphAt 𝓘(Real, Hemisphere.Plane v) (𝓡 2) ∞ f x) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace Real (Fin 3)) (EuclideanSpace Real (Fin 3)) ∞,
      F '' closedBall 0 1 = closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : Hemisphere.Plane v) r,
        F (f x) = (Hemisphere.toSphere hv x : EuclideanSpace Real (Fin 3)) := by
  obtain ⟨e, hes, _, heq, he, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact
      (isCompact_closedBall 0 r) hinj hloc
  let d := Hemisphere.chart hv
  have hcenter' : e 0 = d 0 := by
    apply Subtype.ext
    rw [heq (hes (mem_closedBall_self hr.le)), hcenter]
    exact (Hemisphere.chart_zero hv).symm
  obtain ⟨L, _, K, _, _, P, hP0, hPs, _, hP⟩ :=
    exists_supported_ball_straightening e d he hei
      (Hemisphere.contMDiff_chart hv).contMDiffOn
      (Hemisphere.contMDiffOn_chart_symm hv) hr hes (mem_univ _) hcenter'
  obtain ⟨Q, hQball, hQrad⟩ :=
    Poincare.Manifold.exists_sphere_diffeomorph_extension_of_isotopy
      (P 1) (LinearIsometryEquiv.refl Real E3) P hPs
      (fun p => congrArg Subtype.val (hP0 p)) (fun _ => rfl)
  have hQ (p : S2) : Q p = (P 1 p : E3) := by
    simpa only [one_smul] using hQrad p 1 (by norm_num)
  let A := Hemisphere.extendLinear v L.symm
  let N := LinearBall.neighborhood A
  let b := Q.toHomeomorph.toOpenPartialHomeomorph.trans N
  have hbs : closedBall (0 : E3) 1 ⊆ b.source := by
    intro x hx
    exact ⟨mem_univ _, LinearBall.closedBall_subset_source A
      (hQball ▸ mem_image_of_mem Q hx)⟩
  have hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source :=
    (LinearBall.contMDiffOn_neighborhood A).comp
      Q.contMDiff.contMDiffOn inter_subset_right
  have hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target :=
    Q.symm.contMDiff.comp_contMDiffOn
      ((LinearBall.contMDiffOn_neighborhood_symm A).mono inter_subset_left)
  let B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toPartialEquiv := b.toPartialEquiv
    open_source := b.open_source
    open_target := b.open_target
    contMDiffOn_toFun := hb
    contMDiffOn_invFun := hbi }
  obtain ⟨F, hF⟩ := exists_global_extension_of_local_ball_embedding zero_lt_one b
    (b.injOn.mono hbs) (fun x hx => ⟨B, hbs hx, fun _ _ => rfl⟩)
  refine ⟨F, ?_, ?_⟩
  · calc
      F '' closedBall 0 1 = b '' closedBall 0 1 := image_congr (fun x hx => hF x hx)
      _ = N '' (Q '' closedBall 0 1) := (image_image N Q _).symm
      _ = closedBall 0 1 := by rw [hQball]; exact LinearBall.image_closedBall A
  · intro x hx
    rw [hF (f x) (sphere_subset_closedBall (f x).property)]
    change N (Q (f x)) = _
    rw [hQ, ← heq (hes hx), hP x hx]
    rw [LinearBall.apply_of_mem_sphere A (d (L x)).property]
    change ‖A (Hemisphere.chart hv (L x) : E3)‖⁻¹ •
      A (Hemisphere.chart hv (L x) : E3) = _
    rw [Hemisphere.normalized_linear_chart hv A L.symm
      (Hemisphere.extendLinear_center L.symm) (Hemisphere.extendLinear_plane L.symm),
      L.symm_apply_apply]
    rfl



theorem exists_marked_disk_round_coordinates
    {r : Real} (hr : 0 < r)
    (f : EuclideanSpace Real (Fin 2) -> S2)
    (hinj : InjOn f (closedBall 0 r))
    (hloc : ∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin 2)) r,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x) :
    ∃ J : EuclideanSpace Real (Fin 2) ≃ₗᵢ[Real] Hemisphere.Plane (f 0 : E3),
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        F '' closedBall 0 1 = closedBall 0 1 ∧
        ∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin 2)) r,
          F (f x) = (Hemisphere.toSphere (norm_eq_of_mem_sphere (f 0)) (J x) : E3) := by
  let J : EuclideanSpace Real (Fin 2) ≃ₗᵢ[Real] Hemisphere.Plane (f 0 : E3) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2
      (ne_zero_of_mem_unit_sphere (f 0))).repr.symm
  let g : Hemisphere.Plane (f 0 : E3) -> S2 := f ∘ J.symm
  have hJ (x : Hemisphere.Plane (f 0 : E3)) (hx : x ∈ closedBall 0 r) :
      J.symm x ∈ closedBall 0 r := by
    simpa only [mem_closedBall, dist_zero_right, J.symm.norm_map] using hx
  obtain ⟨F, hFball, hF⟩ := exists_marked_ball_normalization (f 0)
    (norm_eq_of_mem_sphere (f 0)) hr g (by simp [g])
    (fun x hx y hy hxy => J.symm.injective (hinj (hJ x hx) (hJ y hy) hxy))
    (fun x hx => (J.symm.toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph x).comp
      (𝓡 2) S2 (hloc _ (hJ x hx)))
  refine ⟨J, F, hFball, fun x hx => ?_⟩
  have hxJ : J x ∈ closedBall 0 r := by
    simpa only [mem_closedBall, dist_zero_right, J.norm_map] using hx
  simpa only [g, Function.comp_apply, J.symm_apply_apply] using hF (J x) hxJ

end Poincare.Manifold.Schoenflies
