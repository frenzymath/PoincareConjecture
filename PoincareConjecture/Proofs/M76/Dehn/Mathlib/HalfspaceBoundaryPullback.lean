import PoincareConjecture.Proofs.M76.Mathlib.CoveringPLAtlas

set_option autoImplicit false

open Set Geometry

namespace IsLocalHomeomorph

variable {X M E ι κ : Type*} [TopologicalSpace X] [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem halfspace_boundary_preimage
    {p : X → M} (hp : IsLocalHomeomorph p)
    (e : ι → OpenPartialHomeomorph M E)
    (d : κ → OpenPartialHomeomorph X E) (index : κ → ι)
    (hdtarget : ∀ k, (d k).target ⊆ (e (index k)).target)
    (hdinv : ∀ k, EqOn (p ∘ (d k).symm) (e (index k)).symm (d k).target)
    {R : Set M}
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∀ x ∈ frontier (p ⁻¹' R),
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph X E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ k, (d k).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ p ⁻¹' R ↔ 0 ≤ ell (B y) := by
  intro x hx
  have hpx : p x ∈ frontier R := by
    rw [← hp.isOpenMap.preimage_frontier_eq_frontier_preimage hp.continuous R] at hx
    exact hx
  obtain ⟨ell, v, B, hv, hxB, hellx, hcompat, hcut⟩ := hboundary (p x) hpx
  let B' : OpenPartialHomeomorph X E := (hp.localInverseAt x).symm.trans B
  have hval : (B' : X → E) = B ∘ p := by
    funext y
    change B ((hp.localInverseAt x).symm y) = B (p y)
    rw [hp.localInverseAt_symm]
  have hsource : MapsTo p B'.source B.source := by
    intro y hy
    change y ∈ (hp.localInverseAt x).target ∧
      (hp.localInverseAt x).symm y ∈ B.source at hy
    simpa only [hp.localInverseAt_symm] using hy.2
  have hxB' : x ∈ B'.source := by
    change x ∈ (hp.localInverseAt x).target ∧
      (hp.localInverseAt x).symm x ∈ B.source
    simpa only [hp.self_mem_localInverseAt_target, hp.localInverseAt_symm, true_and]
      using hxB
  refine ⟨ell, v, B', hv, hxB', ?_, ?_, ?_⟩
  · rw [hval]
    exact hellx
  · intro k
    have hsub : ((d k).symm.trans B').source ⊆
        ((e (index k)).symm.trans B).source := by
      intro z hz
      refine ⟨hdtarget k hz.1, ?_⟩
      have h := hsource hz.2
      have he : p ((d k).symm z) = (e (index k)).symm z := hdinv k hz.1
      change p ((d k).symm z) ∈ B.source at h
      change (e (index k)).symm z ∈ B.source
      exact he ▸ h
    have heq : EqOn ((d k).symm.trans B')
        ((e (index k)).symm.trans B) ((d k).symm.trans B').source := by
      intro z hz
      change B' ((d k).symm z) = B ((e (index k)).symm z)
      rw [hval]
      exact congrArg B (hdinv k hz.1)
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact (((mem_piecewiseAffineGroupoid_iff_forward _).mp (hcompat (index k))).mono
      ((d k).symm.trans B').open_source hsub).congr heq.symm
  · intro y hy
    rw [hval]
    exact hcut (p y) (hsource hy)

theorem exists_halfspace_coordinate_cover_over
    {p : X → M} (hp : IsLocalHomeomorph p)
    (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    {R : Set M}
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ d : ι × X → OpenPartialHomeomorph X E,
      (∀ x, ∃ k, x ∈ (d k).source) ∧
      (∀ i x, x ∈ (d (i, x)).source ↔ p x ∈ (e i).source) ∧
      (∀ k, MapsTo p (d k).source (e k.1).source) ∧
      (∀ k, (d k).target ⊆ (e k.1).target) ∧
      (∀ k, (d k : X → E) = (e k.1) ∘ p) ∧
      (∀ k, EqOn (p ∘ (d k).symm) (e k.1).symm (d k).target) ∧
      (∀ k l, (d k).symm.trans (d l) ∈ piecewiseAffineGroupoid E) ∧
      ∀ x ∈ frontier (p ⁻¹' R),
        ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph X E),
          ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
          (∀ k, (d k).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
          ∀ y ∈ B.source, y ∈ p ⁻¹' R ↔ 0 ≤ ell (B y) := by
  obtain ⟨d, hdcover, hdcenter, hdsource, hdtarget, hdval, hdinv, hdcompat⟩ :=
    hp.exists_piecewiseAffine_coordinate_cover_over e hcover hcompat
  exact ⟨d, hdcover, hdcenter, hdsource, hdtarget, hdval, hdinv, hdcompat,
    hp.halfspace_boundary_preimage e d Prod.fst hdtarget hdinv hboundary⟩

end IsLocalHomeomorph
