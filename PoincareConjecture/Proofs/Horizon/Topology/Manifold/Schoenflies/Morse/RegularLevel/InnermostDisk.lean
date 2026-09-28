import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.PlanarTube
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private abbrev Plane (v : E3) := (Real ∙ v)ᗮ
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private theorem normalize_circle_in_plane {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Plane v) ∞ γ) :
    ∃ A : Diffeomorph 𝓘(Real, Plane v) 𝓘(Real, Plane v) (Plane v) (Plane v) ∞,
      A '' sphere (0 : Plane v) 1 = range γ := by
  let J : Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr
  have hJ : ContMDiff 𝓘(Real, Plane v) (𝓡 2) ∞ J.toContinuousLinearEquiv :=
    J.toContinuousLinearEquiv.contDiff.contMDiff
  have hemb : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (J ∘ γ) := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (hJ.comp hγ.contMDiff) (J.injective.comp hγ.isEmbedding.injective)
    intro p
    rw [mfderiv_comp p (hJ.mdifferentiable (by simp) _)
      (hγ.contMDiff.mdifferentiable (by simp) p)]
    exact (J.toContinuousLinearEquiv.toDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (γ p)).injective.comp
      ((hγ.isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf (by simp))
  obtain ⟨B, hB⟩ := exists_ambient_diffeomorph_of_smooth_circle (J ∘ γ) hemb
  let A := (J.toContinuousLinearEquiv.toDiffeomorph.trans B).trans
    J.symm.toContinuousLinearEquiv.toDiffeomorph
  refine ⟨A, ?_⟩
  change (fun x => J.symm (B (J x))) '' sphere (0 : Plane v) 1 = range γ
  rw [← image_image J.symm (fun x => B (J x)), ← image_image B J,
    J.image_sphere, map_zero, hB]
  ext y
  constructor
  · rintro ⟨z, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, (J.symm_apply_apply _).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨J (γ q), mem_range_self q, J.symm_apply_apply _⟩

theorem exists_innermost_regular_level_disk_of_smooth
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hne : (h ⁻¹' {c}).Nonempty) :
    ∃ p : S2, h p = c ∧
      ∃ A : Diffeomorph 𝓘(Real, Plane v) 𝓘(Real, Plane v) (Plane v) (Plane v) ∞,
        A '' sphere (0 : Plane v) 1 =
          (fun x => (Plane v).orthogonalProjectionOnto (f x)) ''
            connectedComponentIn (h ⁻¹' {c}) p ∧
        ((fun x : Plane v => c • v + (A x : E3)) '' closedBall (0 : Plane v) 1) ∩
          range f = f '' connectedComponentIn (h ⁻¹' {c}) p := by
  classical
  let L : Set S2 := h ⁻¹' {c}
  let : Finite (ConnectedComponents L) :=
    Poincare.Geometry.Manifold.RegularLevel.finite_connectedComponents_of_compact_regular_level
      hh c ((isClosed_singleton.preimage hh.continuous).isCompact) hc
  let : Nonempty L := hne.to_subtype
  let rep : ConnectedComponents L → L := fun i =>
    Classical.choose (ConnectedComponents.surjective_coe i)
  have hrep (i : ConnectedComponents L) : ConnectedComponents.mk (rep i) = i :=
    Classical.choose_spec (ConnectedComponents.surjective_coe i)
  let C : ConnectedComponents L → Set S2 := fun i => connectedComponentIn L (rep i).val
  let q : S2 → Plane v := fun x => (Plane v).orthogonalProjectionOnto (f x)
  have hindex (i : ConnectedComponents L) {x : S2} (hx : x ∈ C i) :
      ∃ hxL : x ∈ L, ConnectedComponents.mk (⟨x, hxL⟩ : L) = i := by
    rw [show C i = connectedComponentIn L (rep i).val from rfl,
      connectedComponentIn_eq_image (rep i).property] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y.property, (ConnectedComponents.coe_eq_coe'.mpr hy).trans (hrep i)⟩
  have hmem (x : L) : x.val ∈ C (ConnectedComponents.mk x) := by
    rw [show C (ConnectedComponents.mk x) =
      connectedComponentIn L (rep (ConnectedComponents.mk x)).val from rfl,
      connectedComponentIn_eq_image (rep _).property]
    exact ⟨x, ConnectedComponents.coe_eq_coe'.mp (hrep _).symm, rfl⟩
  have hnorm (i : ConnectedComponents L) :
      ∃ A : Diffeomorph 𝓘(Real, Plane v) 𝓘(Real, Plane v) (Plane v) (Plane v) ∞,
        A '' sphere (0 : Plane v) 1 = q '' C i := by
    obtain ⟨ε, hε, F, hs, hF, hFi, hl, hcenter, r, hr, hrε, γ, hγ, hemb, hγrange, hγeq⟩ :=
      exists_smooth_planar_family_of_regular_level_component_of_smooth hf hh hv hheight c hc
        (rep i).val (rep i).property
    obtain ⟨A, hA⟩ := normalize_circle_in_plane hv (fun x => γ (0, x)) (hemb 0)
    exact ⟨A, hA.trans hγrange⟩
  choose A hA using hnorm
  have hqinj : InjOn q L := by
    have hi := Poincare.Geometry.Manifold.injective_projection_of_height_eq hv
      (fun x : L => (hheight x.val).trans x.property)
      (hf.isEmbedding.injective.comp Subtype.val_injective)
    intro x hx y hy hxy
    exact congrArg Subtype.val (@hi ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  have hdisj : (univ : Set (ConnectedComponents L)).Pairwise fun i j =>
      Disjoint (A i '' sphere (0 : Plane v) 1) (A j '' sphere (0 : Plane v) 1) := by
    intro i hi j hj hij
    rw [hA i, hA j]
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    obtain ⟨hxL, hxi⟩ := hindex i hx
    obtain ⟨hzL, hzj⟩ := hindex j hz
    have hzx := hqinj hzL hxL heq
    subst z
    exact hij (hxi.symm.trans hzj)
  have hv0 : v ≠ 0 := by intro heq; simp [heq] at hv
  have hdim : 1 < Module.rank Real (Plane v) := by
    rw [← Module.finrank_eq_rank, Submodule.finrank_orthogonal_span_singleton (n := 2) hv0]
    norm_num
  let : Nontrivial (Plane v) := Module.nontrivial_of_finrank_pos (by
    rw [Submodule.finrank_orthogonal_span_singleton (n := 2) hv0]
    norm_num)
  obtain ⟨i, _, hinner⟩ := exists_innermost_image_closedBall
    (fun i => (A i).toHomeomorph) hdim (Set.toFinite univ) Set.univ_nonempty hdisj
  refine ⟨(rep i).val, (rep i).property, A i, hA i, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, rfl⟩⟩
    have hzL : z ∈ L := by
      change h z = c
      rw [← hheight z, ← hxy]
      have horth := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A i x).property
      simp [inner_add_right, inner_smul_right, horth, hv]
    have hqz : q z = A i x := by
      rw [show q z = (Plane v).orthogonalProjectionOnto (f z) from rfl, ← hxy]
      simp [Plane, map_add, map_smul,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
    let j : ConnectedComponents L := ConnectedComponents.mk (⟨z, hzL⟩ : L)
    have hzC : z ∈ C j := hmem ⟨z, hzL⟩
    have hji : j = i := by
      by_contra hneji
      have hb : q z ∈ A j '' sphere (0 : Plane v) 1 := by
        rw [hA j]
        exact ⟨z, hzC, rfl⟩
      exact disjoint_left.mp (hinner j (mem_univ _) hneji)
        ⟨x, hx, hqz.symm⟩ hb
    exact ⟨z, hji ▸ hzC, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzL : z ∈ L := connectedComponentIn_subset L _ hz
    have hqz : q z ∈ A i '' sphere (0 : Plane v) 1 := by
      rw [hA i]
      exact ⟨z, hz, rfl⟩
    obtain ⟨x, hx, heq⟩ := hqz
    refine ⟨⟨x, sphere_subset_closedBall hx, ?_⟩, mem_range_self z⟩
    have hdecomp := Poincare.Geometry.Manifold.eq_height_smul_add_projection hv
      (fun z : L => (hheight z.val).trans z.property) (⟨z, hzL⟩ : L)
    change c • v + (A i x : E3) = f z
    rw [heq]
    exact hdecomp.symm

theorem exists_innermost_regular_level_disk
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hne : (h ⁻¹' {c}).Nonempty) :
    ∃ p : S2, h p = c ∧
      ∃ A : Diffeomorph 𝓘(Real, Plane v) 𝓘(Real, Plane v) (Plane v) (Plane v) ∞,
        A '' sphere (0 : Plane v) 1 =
          (fun x => (Plane v).orthogonalProjectionOnto (f x)) ''
            connectedComponentIn (h ⁻¹' {c}) p ∧
        ((fun x : Plane v => c • v + (A x : E3)) '' closedBall (0 : Plane v) 1) ∩
          range f = f '' connectedComponentIn (h ⁻¹' {c}) p :=
  (fun _ => exists_innermost_regular_level_disk_of_smooth hf hh hv hheight c hc hne) hfinite

end Poincare.Manifold.Schoenflies
