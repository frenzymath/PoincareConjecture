import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩



theorem exists_boundary_reparametrization_of_filling
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hboundary : F '' sphere (0 : E3) 1 = range f) :
    ∃ q : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
      ∀ p : S2, F (q p : E3) = f p := by
  have hmem (p : S2) : F.symm (f p) ∈ sphere (0 : E3) 1 := by
    obtain ⟨x, hx, hxp⟩ := hboundary.symm ▸ mem_range_self p
    rw [← hxp, F.symm_apply_apply]
    exact hx
  let Q : S2 → S2 := fun p => ⟨F.symm (f p), hmem p⟩
  have hQ (p : S2) : F (Q p : E3) = f p := F.apply_symm_apply (f p)
  have hQs : ContMDiff (𝓡 2) (𝓡 2) ∞ Q :=
    (F.symm.contMDiff.comp hf.contMDiff).codRestrict_sphere hmem
  have hQbij : Bijective Q := by
    constructor
    · intro p q hpq
      apply hf.isEmbedding.injective
      rw [← hQ p, ← hQ q, hpq]
    · intro p
      obtain ⟨q, hq⟩ := hboundary ▸ mem_image_of_mem F p.property
      refine ⟨q, ?_⟩
      apply Subtype.ext
      change F.symm (f q) = (p : E3)
      rw [hq, F.symm_apply_apply]
  let B : S2 → E3 := fun p => F p
  have hB : ContMDiff (𝓡 2) (𝓡 3) ∞ B := F.contMDiff.comp contMDiff_coe_sphere
  have hfactor : f = B ∘ Q := funext fun p => (hQ p).symm
  have hQderiv (p : S2) : Bijective (mfderiv (𝓡 2) (𝓡 2) Q p) := by
    have hfinj := injective_mfderiv_sphere_embedding hf p
    have hchain := mfderiv_comp p ((hB (Q p)).mdifferentiableAt (by simp))
      ((hQs p).mdifferentiableAt (by simp))
    rw [← hfactor] at hchain
    have hinj : Injective (mfderiv (𝓡 2) (𝓡 2) Q p) := by
      intro u v huv
      apply hfinj
      rw [hchain]
      exact congrArg (mfderiv (𝓡 2) (𝓡 3) B (Q p)) huv
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E2) (V₂ := E2)
      (f := (mfderiv (𝓡 2) (𝓡 2) Q p).toLinearMap) rfl).mp hinj⟩
  let hlocal := Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hQs hQderiv
  exact ⟨hlocal.diffeomorphOfBijective hQbij, hQ⟩



theorem exists_marked_disk_of_filling
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hboundary : F '' sphere (0 : E3) 1 = range f)
    (d : OpenPartialHomeomorph E2 S2)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hsource : closedBall (0 : E2) 1 ⊆ d.source) :
    ∃ m : E2 → S2,
      InjOn m (closedBall 0 1) ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) ∧
      (∀ x, F (m x : E3) = f (d x)) := by
  obtain ⟨q, hq⟩ := exists_boundary_reparametrization_of_filling hf F hboundary
  let D : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ := {
    toPartialEquiv := d.toPartialEquiv
    open_source := d.open_source
    open_target := d.open_target
    contMDiffOn_toFun := hd
    contMDiffOn_invFun := hdi }
  refine ⟨q ∘ d, ?_, ?_, fun x => hq (d x)⟩
  · intro x hx y hy hxy
    exact d.injOn (hsource hx) (hsource hy) (q.injective hxy)
  · intro x hx
    have hloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ d x :=
      ⟨D, hsource hx, fun _ _ => rfl⟩
    exact hloc.comp (𝓡 2) S2 (q.isLocalDiffeomorph (d x))




theorem exists_marked_cap_of_filling
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hboundary : F '' sphere (0 : E3) 1 = range f)
    (d : OpenPartialHomeomorph E2 S2)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hsource : closedBall (0 : E2) 1 ⊆ d.source)
    (g : E2 → E3)
    (hpatch : ∀ x ∈ closedBall (0 : E2) 1, f (d x) = g x) :
    ∃ m : E2 → S2,
      InjOn m (closedBall 0 1) ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) ∧
      (∀ x ∈ closedBall (0 : E2) 1, F (m x : E3) = g x) ∧
      (fun x => F (m x : E3)) '' closedBall (0 : E2) 1 =
        g '' closedBall (0 : E2) 1 ∧
      (fun x => F (m x : E3)) '' sphere (0 : E2) 1 =
        g '' sphere (0 : E2) 1 := by
  obtain ⟨m, hmi, hml, hm⟩ := exists_marked_disk_of_filling hf F hboundary d hd hdi hsource
  have heq : EqOn (fun x => F (m x : E3)) g (closedBall (0 : E2) 1) :=
    fun x hx => (hm x).trans (hpatch x hx)
  exact ⟨m, hmi, hml, heq, image_congr heq,
    image_congr (heq.mono sphere_subset_closedBall)⟩

end Poincare.Manifold.Schoenflies.Reverse
