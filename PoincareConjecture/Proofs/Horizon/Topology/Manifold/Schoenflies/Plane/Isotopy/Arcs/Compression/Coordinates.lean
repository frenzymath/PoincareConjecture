import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallStraightening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.LinearBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Compression

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩



theorem exists_marked_disk_normalization
    (v : EuclideanSpace Real (Fin 2)) (hv : ‖v‖ = 1)
    {r : Real} (hr : 0 < r)
    (f : Hemisphere.Plane v -> sphere (0 : EuclideanSpace Real (Fin 2)) 1)
    (hcenter : (f 0 : EuclideanSpace Real (Fin 2)) = v)
    (hinj : InjOn f (closedBall 0 r))
    (hloc : ∀ x ∈ closedBall (0 : Hemisphere.Plane v) r,
      IsLocalDiffeomorphAt 𝓘(Real, Hemisphere.Plane v) (𝓡 1) ∞ f x) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2)
        (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
      F '' closedBall 0 1 = closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : Hemisphere.Plane v) r,
        F (f x) = (Hemisphere.toSphere hv x : EuclideanSpace Real (Fin 2)) := by
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
  obtain ⟨Q, hQ, hQball, _⟩ :=
    exists_ambient_diffeomorph_of_circle_diffeomorph (P 1)
  let A := Hemisphere.extendLinear v L.symm
  let N := LinearBall.neighborhood A
  let b := Q.toHomeomorph.toOpenPartialHomeomorph.trans N
  have hbs : closedBall (0 : E2) 1 ⊆ b.source := by
    intro x hx
    exact ⟨mem_univ _, LinearBall.closedBall_subset_source A
      (hQball ▸ mem_image_of_mem Q hx)⟩
  have hb : ContMDiffOn (𝓡 2) (𝓡 2) ∞ b b.source :=
    (LinearBall.contMDiffOn_neighborhood A).comp
      Q.contMDiff.contMDiffOn inter_subset_right
  have hbi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ b.symm b.target :=
    Q.symm.contMDiff.comp_contMDiffOn
      ((LinearBall.contMDiffOn_neighborhood_symm A).mono inter_subset_left)
  let B : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ := {
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
    change ‖A (Hemisphere.chart hv (L x) : E2)‖⁻¹ •
      A (Hemisphere.chart hv (L x) : E2) = _
    rw [Hemisphere.normalized_linear_chart hv A L.symm
      (Hemisphere.extendLinear_center L.symm) (Hemisphere.extendLinear_plane L.symm),
      L.symm_apply_apply]
    rfl



theorem exists_marked_arc_round_coordinates
    {r : Real} (hr : 0 < r)
    (f : EuclideanSpace Real (Fin 1) -> S1)
    (hinj : InjOn f (closedBall 0 r))
    (hloc : ∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin 1)) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x) :
    ∃ J : EuclideanSpace Real (Fin 1) ≃ₗᵢ[Real] Hemisphere.Plane (f 0 : E2),
      ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        F '' closedBall 0 1 = closedBall 0 1 ∧
        ∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin 1)) r,
          F (f x) = (Hemisphere.toSphere (norm_eq_of_mem_sphere (f 0)) (J x) : E2) := by
  let J : EuclideanSpace Real (Fin 1) ≃ₗᵢ[Real] Hemisphere.Plane (f 0 : E2) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (ne_zero_of_mem_unit_sphere (f 0))).repr.symm
  let g : Hemisphere.Plane (f 0 : E2) -> S1 := f ∘ J.symm
  have hJ (x : Hemisphere.Plane (f 0 : E2)) (hx : x ∈ closedBall 0 r) :
      J.symm x ∈ closedBall 0 r := by
    simpa only [mem_closedBall, dist_zero_right, J.symm.norm_map] using hx
  obtain ⟨F, hFball, hF⟩ := exists_marked_disk_normalization (f 0)
    (norm_eq_of_mem_sphere (f 0)) hr g (by simp [g])
    (fun x hx y hy hxy => J.symm.injective (hinj (hJ x hx) (hJ y hy) hxy))
    (fun x hx => (J.symm.toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph x).comp
      (𝓡 1) S1 (hloc _ (hJ x hx)))
  refine ⟨J, F, hFball, fun x hx => ?_⟩
  have hxJ : J x ∈ closedBall 0 r := by
    simpa only [mem_closedBall, dist_zero_right, J.norm_map] using hx
  simpa only [g, Function.comp_apply, J.symm_apply_apply] using hF (J x) hxJ

namespace Normalization

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1



theorem exists_ambient_disk_normalization
    (b : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (g : E1 → S1)
    (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E1) 1,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x) :
    ∃ J : E1 ≃ₗᵢ[Real] Hemisphere.Plane (g 0 : E2),
      ∃ H : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        H '' (b '' closedBall 0 1) = closedBall 0 1 ∧
        H '' (b '' ball 0 1) = ball 0 1 ∧
        H '' (b '' sphere 0 1) = sphere 0 1 ∧
        (∀ x ∈ closedBall (0 : E1) 1,
          H (b (g x)) = (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) (J x) : E2)) ∧
        H '' ((fun x => b (g x)) '' closedBall (0 : E1) 1) =
          (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E2)) ''
            closedBall (0 : Hemisphere.Plane (g 0 : E2)) 1 ∧
        H '' ((fun x => b (g x)) '' ball (0 : E1) 1) =
          (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E2)) ''
            ball (0 : Hemisphere.Plane (g 0 : E2)) 1 ∧
        H '' ((fun x => b (g x)) '' sphere (0 : E1) 1) =
          (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E2)) ''
            sphere (0 : Hemisphere.Plane (g 0 : E2)) 1 := by
  obtain ⟨J, N, hNball, hNdisk⟩ :=
    exists_marked_arc_round_coordinates zero_lt_one g hgi hgl
  let H := b.symm.trans N
  have hHb (x : E2) : H (b x) = N x := by
    change N (b.symm (b x)) = N x
    rw [b.symm_apply_apply]
  have hHball : H '' (b '' closedBall (0 : E2) 1) = closedBall 0 1 := by
    rw [image_image]
    calc
      (fun x => H (b x)) '' closedBall (0 : E2) 1 = N '' closedBall 0 1 :=
        image_congr (fun x _ => hHb x)
      _ = closedBall 0 1 := hNball
  have hHopen : H '' (b '' ball (0 : E2) 1) = ball 0 1 := by
    have h := congrArg interior hHball
    change interior (H.toHomeomorph '' (b.toHomeomorph '' closedBall (0 : E2) 1)) =
      interior (closedBall (0 : E2) 1) at h
    rw [← H.toHomeomorph.image_interior, ← b.toHomeomorph.image_interior,
      interior_closedBall (0 : E2) one_ne_zero] at h
    exact h
  have hHsphere : H '' (b '' sphere (0 : E2) 1) = sphere 0 1 := by
    have h := congrArg frontier hHball
    change frontier (H.toHomeomorph '' (b.toHomeomorph '' closedBall (0 : E2) 1)) =
      frontier (closedBall (0 : E2) 1) at h
    rw [← H.toHomeomorph.image_frontier, ← b.toHomeomorph.image_frontier,
      frontier_closedBall (0 : E2) one_ne_zero] at h
    exact h
  have hHdisk (x : E1) (hx : x ∈ closedBall 0 1) :
      H (b (g x)) = (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) (J x) : E2) := by
    rw [hHb]
    exact hNdisk x hx
  have himage (s : Set E1) (hs : s ⊆ closedBall 0 1) :
      H '' ((fun x => b (g x)) '' s) =
        (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E2)) '' (J '' s) := by
    rw [image_image, image_image]
    exact image_congr (fun x hx => hHdisk x (hs hx))
  refine ⟨J, H, hHball, hHopen, hHsphere, hHdisk, ?_, ?_, ?_⟩
  · rw [himage _ Subset.rfl, J.image_closedBall]
    simp only [map_zero]
  · rw [himage _ ball_subset_closedBall, J.image_ball]
    simp only [map_zero]
  · rw [himage _ sphere_subset_closedBall, J.image_sphere]
    simp only [map_zero]

end Normalization

end Poincare.Manifold.Schoenflies.PlaneArcs.Compression
