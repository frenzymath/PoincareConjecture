import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.DiskComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.ParallelDisks.Charts



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private theorem sphere_restriction
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hball : F '' closedBall 0 1 = closedBall 0 1) :
    ∃ d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞, ∀ p : S2, (d p : E3) = F p := by
  have hs : F '' sphere (0 : E3) 1 = sphere 0 1 := by
    have h := F.toHomeomorph.image_frontier (closedBall (0 : E3) 1)
    change F '' frontier (closedBall 0 1) = frontier (F '' closedBall 0 1) at h
    simpa only [hball, frontier_closedBall _ one_ne_zero] using h
  have hi (p : S2) : F.symm p ∈ sphere (0 : E3) 1 := by
    obtain ⟨x, hx, heq⟩ := hs.superset p.property
    rwa [← heq, F.symm_apply_apply]
  let e : S2 ≃ S2 := {
    toFun := fun p => ⟨F p, hs.subset (mem_image_of_mem F p.property)⟩
    invFun := fun p => ⟨F.symm p, hi p⟩
    left_inv := fun p => Subtype.ext (F.symm_apply_apply p)
    right_inv := fun p => Subtype.ext (F.apply_symm_apply p) }
  exact ⟨{
    toEquiv := e
    contMDiff_toFun := (F.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _
    contMDiff_invFun := (F.symm.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _ },
    fun _ => rfl⟩




theorem exists_global_complementary_disk_chart
    (m : E2 → S2) (hmi : InjOn m (closedBall 0 1))
    (hml : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) :
    ∃ e : OpenPartialHomeomorph E2 S2,
      e.source = univ ∧
      ContMDiff (𝓡 2) (𝓡 2) ∞ e ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      e '' closedBall 0 1 = (m '' ball 0 1)ᶜ ∧
      e '' ball 0 1 = (m '' closedBall 0 1)ᶜ := by
  obtain ⟨J, F, hFball, hF⟩ := exists_marked_disk_round_coordinates zero_lt_one m hmi hml
  obtain ⟨d, hd⟩ := sphere_restriction F hFball
  let v : E3 := m 0
  have hv : ‖v‖ = 1 := norm_eq_of_mem_sphere (m 0)
  have hdm (x : E2) (hx : x ∈ closedBall 0 1) :
      d (m x) = Hemisphere.toSphere hv (J x) := by
    apply Subtype.ext
    exact (hd (m x)).trans (hF x hx)
  have hJball (r : Real) : J '' ball (0 : E2) r = ball 0 r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_ball_zero_iff, J.norm_map] using hy
    · intro hx
      exact ⟨J.symm x, by simpa only [mem_ball_zero_iff, J.symm.norm_map] using hx,
        J.apply_symm_apply x⟩
  have hJclosed (r : Real) : J '' closedBall (0 : E2) r = closedBall 0 r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_closedBall_zero_iff, J.norm_map] using hy
    · intro hx
      exact ⟨J.symm x, by simpa only [mem_closedBall_zero_iff, J.symm.norm_map] using hx,
        J.apply_symm_apply x⟩
  have hmark : d '' (m '' ball 0 1) =
      Hemisphere.toSphere hv '' ball (0 : Hemisphere.Plane v) 1 := by
    rw [image_image]
    calc
      _ = (fun x => Hemisphere.toSphere hv (J x)) '' ball 0 1 :=
        image_congr (fun x hx => hdm x (ball_subset_closedBall hx))
      _ = _ := by rw [← image_image, hJball]
  let R := Hemisphere.complementRadius (Hemisphere.capHeight 1)
  have hR : 0 < R := Hemisphere.complementRadius_pos
    (by linarith [Hemisphere.capHeight_pos 1]) (Hemisphere.capHeight_lt_one zero_lt_one)
  let Q : E2 ≃L[Real] E2 :=
    (LinearEquiv.smulOfNeZero Real E2 R hR.ne').toContinuousLinearEquiv
  have hQ : Q '' closedBall (0 : E2) 1 = closedBall 0 R := by
    change (fun x : E2 => R • x) '' closedBall 0 1 = _
    rw [image_smul, _root_.smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos hR, mul_one]
  let c := (J.toHomeomorph.toOpenPartialHomeomorph.trans (stereographic hv).symm).trans
    d.symm.toHomeomorph.toOpenPartialHomeomorph
  let e := Q.toHomeomorph.toOpenPartialHomeomorph.trans c
  have hes : e.source = univ := by
    ext x
    change ((x ∈ univ ∧ ((Q x ∈ univ ∧ J (Q x) ∈ univ) ∧
      stereoInvFun hv (J (Q x)) ∈ univ))) ↔ x ∈ univ
    simp
  have he : ContMDiff (𝓡 2) (𝓡 2) ∞ e :=
    d.symm.contMDiff.comp ((Hemisphere.contMDiff_stereoInvFun hv).comp
      (J.toContinuousLinearEquiv.contDiff.contMDiff.comp Q.contDiff.contMDiff))
  have hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target := by
    apply Q.symm.contDiff.contMDiff.comp_contMDiffOn
    apply J.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp_contMDiffOn
    apply (Hemisphere.contMDiffOn_stereographic hv).comp d.contMDiff.contMDiffOn
    intro p hp
    exact hp.1.2.1
  have hec : e '' closedBall (0 : E2) 1 = (m '' ball 0 1)ᶜ := by
    change (fun x => d.symm (stereoInvFun hv (J (Q x)))) '' closedBall 0 1 = _
    calc
      _ = d.symm '' (stereoInvFun hv '' (J '' (Q '' closedBall 0 1))) := by
        rw [image_image, image_image, image_image]
      _ = (m '' ball 0 1)ᶜ := by
        rw [hQ, hJclosed, ← Hemisphere.complement_image_ball_toSphere hv zero_lt_one, ← hmark]
        change d.toEquiv.symm '' (d.toEquiv '' (m '' ball 0 1))ᶜ = _
        rw [← d.toEquiv.image_compl, d.toEquiv.symm_image_image]
  obtain ⟨n, hns, _, hnm, _, _⟩ := Poincare.exists_openPartialHomeomorph_of_injOn_compact
    (isCompact_closedBall (0 : E2) 1) hmi hml
  have hnclosed : n '' closedBall (0 : E2) 1 = m '' closedBall 0 1 :=
    image_congr (fun x hx => hnm (hns hx))
  have hnopen : n '' ball (0 : E2) 1 = m '' ball 0 1 :=
    image_congr (fun x hx => hnm (hns (ball_subset_closedBall hx)))
  refine ⟨e, hes, he, hei, hec, ?_⟩
  rw [e.image_ball_eq_interior (hes ▸ subset_univ _) hec, interior_compl,
    ← hnopen, ParallelDisks.closure_image_ball zero_lt_one n hns, hnclosed]




theorem exists_complementary_boundary_parametrization
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (m : E2 → S2) (hmi : InjOn m (closedBall 0 1))
    (hml : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) :
    ∃ g : E2 → E3, ContDiff Real ∞ g ∧ Injective g ∧
      (∀ x, Injective (fderiv Real g x)) ∧
      range g ⊆ B '' sphere (0 : E3) 1 ∧
      g '' closedBall (0 : E2) 1 = (B '' sphere (0 : E3) 1) \
        ((fun x => B (m x : E3)) '' ball (0 : E2) 1) ∧
      (B '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) =
        (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 := by
  obtain ⟨e, hes, he, hei, heclosed, heopen⟩ :=
    exists_global_complementary_disk_chart m hmi hml
  let k : S2 → E3 := fun p => B (p : E3)
  let g : E2 → E3 := k ∘ e
  have hk : Injective k := B.injective.comp Subtype.val_injective
  have hks : k '' univ = B '' sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨p, _, rfl⟩
      exact mem_image_of_mem B p.property
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  have hcomplement (S : Set S2) :
      k '' Sᶜ = (B '' sphere (0 : E3) 1) \ (k '' S) := by
    calc
      _ = (k '' univ) \ (k '' S) := by
        rw [compl_eq_univ_sdiff]
        exact image_sdiff hk univ S
      _ = _ := by rw [hks]
  have hkg : ContMDiff (𝓡 2) (𝓡 3) ∞ k := B.contMDiff.comp contMDiff_coe_sphere
  have hg : ContDiff Real ∞ g := (hkg.comp he).contDiff
  have hgi : Injective g := hk.comp (by
    intro x y hxy
    exact e.injOn (hes ▸ mem_univ x) (hes ▸ mem_univ y) hxy)
  have hgd (x : E2) : Injective (fderiv Real g x) := by
    let E : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
      { e with contMDiffOn_toFun := he.contMDiffOn, contMDiffOn_invFun := hei }
    have hel := E.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hes ▸ mem_univ x)
    rw [← mfderiv_eq_fderiv]
    change Injective (mfderiv (𝓡 2) (𝓡 3) (k ∘ e) x)
    rw [mfderiv_comp x (hkg.mdifferentiable (by simp) _) (he.mdifferentiable (by simp) x)]
    apply Injective.comp _ (hel.mfderivToContinuousLinearEquiv (by simp)).injective
    change Injective (mfderiv (𝓡 2) (𝓡 3) (B ∘ (Subtype.val : S2 → E3)) (e x))
    rw [mfderiv_comp (e x) (B.contMDiff.mdifferentiable (by simp) _)
      ((contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiable (by simp) _)]
    apply (B.mfderivToContinuousLinearEquiv (by simp) (e x : E3)).injective.comp
    convert! injective_mvfderiv_subtypeVal_sphere (e x)
  have hclosed : g '' closedBall (0 : E2) 1 = (B '' sphere (0 : E3) 1) \
      ((fun x => B (m x : E3)) '' ball (0 : E2) 1) := by
    rw [show g = k ∘ e from rfl, image_comp, heclosed, hcomplement, image_image]
  have hopen : g '' ball (0 : E2) 1 = (B '' sphere (0 : E3) 1) \
      ((fun x => B (m x : E3)) '' closedBall (0 : E2) 1) := by
    rw [show g = k ∘ e from rfl, image_comp, heopen, hcomplement, image_image]
  refine ⟨g, hg, hgi, hgd, ?_, hclosed, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact mem_image_of_mem B (e x).property
  · rw [hopen]
    exact sdiff_sdiff_cancel_left (by
      rintro y ⟨x, _, rfl⟩
      exact mem_image_of_mem B (m x).property)

end Poincare.Manifold.Schoenflies.Saddle.Caps
