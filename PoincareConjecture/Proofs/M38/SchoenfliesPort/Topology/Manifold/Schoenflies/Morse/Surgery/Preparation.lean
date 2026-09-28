import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.InnermostDisk
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.LocalizedFlattening

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private abbrev Plane (v : E3) := (Real ∙ v)ᗮ
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
private instance : ChartedSpace (EuclideanSpace Real (Fin 1) × Real) (S1 × Real) :=
  prodChartedSpace _ _ _ _

theorem exists_prepared_innermost_regular_circle_of_smooth
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hne : (h ⁻¹' {c}).Nonempty) {R : Real} (hR : 0 < R) :
    ∃ p : S2, h p = c ∧ ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, inner Real v (D x) = inner Real v x) ∧
      (∀ x, inner Real v x = c -> D x = x) ∧
      (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - c| ≤ R} ∧
        ∀ x ∉ K, D x = x) ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p => D (f p)) ∧
      ∃ ε : Real, 0 < ε ∧ ε < R ∧
        ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
          T.source = univ ×ˢ Ioo (-ε) ε ∧
          ContMDiffOn Iprod (𝓡 2) ∞ T T.source ∧
          ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target ∧
          range (fun q : S1 => T (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p ∧
          ∃ γ : S1 -> Plane v,
            _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Plane v) ∞ γ ∧
            (∀ q t, t ∈ Ioo (-ε) ε ->
              D (f (T (q, t))) = (c + t) • v + (γ q : E3)) ∧
            ∃ A : Diffeomorph 𝓘(Real, Plane v) 𝓘(Real, Plane v) (Plane v) (Plane v) ∞,
              A '' sphere (0 : Plane v) 1 = range γ ∧
              ((fun x : Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
                range (fun p => D (f p)) =
                  (fun p => D (f p)) '' range (fun q : S1 => T (q, 0)) := by
  obtain ⟨p, hp, A, hA, hintersection⟩ :=
    exists_innermost_regular_level_disk_of_smooth hf hh hv hheight c hc hne
  obtain ⟨ε, hε, F, hsource, hF, hFi, hlevel, hcenter,
    r, hr, hrε, hrR, K, hK, hKR, D, hDheight, hDplane, hDfix, hDflat⟩ :=
    exists_supported_ambient_regular_level_flattening_within_of_smooth hf hh hv hheight c hc p hp
      isOpen_univ (subset_univ _) hR
  have hDemb : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p => D (f p)) := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (D.contMDiff.comp hf.contMDiff) (D.injective.comp hf.isEmbedding.injective)
    intro q
    change Injective (mfderiv (𝓡 2) (𝓡 3) (D ∘ f) q)
    rw [mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) _)
      (hf.contMDiff.mdifferentiable (by simp) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) (f q)).injective.comp
      (injective_mfderiv_sphere_embedding hf q)
  let W : Set (S1 × Real) := univ ×ˢ Ioo (-r) r
  have hW : IsOpen W := isOpen_univ.prod isOpen_Ioo
  have hWF : W ⊆ F.source := by
    rw [hsource]
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  let T := F.restr W
  have hTsource : T.source = W := by
    rw [show T.source = (F.restr W).source from rfl, F.restr_source' W hW,
      inter_eq_right.mpr hWF]
  have hTF : T.source ⊆ F.source := hTsource ▸ hWF
  have hTtarget : T.target ⊆ F.target := by
    intro y hy
    have ht := T.map_target hy
    have heq := T.right_inv hy
    exact heq ▸ F.map_source (hTF ht)
  have hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source := hF.mono hTF
  have hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target := hFi.mono hTtarget
  let γ : S1 -> Plane v := fun q => (Plane v).orthogonalProjectionOnto (f (F (q, 0)))
  have hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Plane v) ∞ γ :=
    smoothEmbedding_projected_tube_slice hf hv hheight F hsource hF hFi hlevel 0
      ⟨by linarith, hε⟩
  have hγrange : range γ =
      (fun x => (Plane v).orthogonalProjectionOnto (f x)) ''
        connectedComponentIn (h ⁻¹' {c}) p := by
    rw [← hcenter, ← range_comp]
    rfl
  have hγlift (q : S1) : f (F (q, 0)) = c • v + (γ q : E3) := by
    exact Poincare.Geometry.Manifold.eq_height_smul_add_projection hv
      (fun q : S1 => (hheight (F (q, 0))).trans (by
        simpa using hlevel q 0 ⟨by linarith, hε⟩)) q
  have hDcenter (q : S1) : D (f (F (q, 0))) = f (F (q, 0)) :=
    hDplane _ ((hheight _).trans (by simpa using hlevel q 0 ⟨by linarith, hε⟩))
  refine ⟨p, hp, D, hDheight, hDplane, ⟨K, hK, fun x hx => (hKR hx).1, hDfix⟩,
    hDemb, r, hr, hrR, T, hTsource, hT, hTi, hcenter, γ, hγ, ?_, A,
    hA.trans hγrange.symm, ?_⟩
  · intro q t ht
    change D (f (F (q, t))) = _
    rw [hDflat t ⟨ht.1.le, ht.2.le⟩ q, hγlift, add_smul]
    abel
  · ext y
    constructor
    · rintro ⟨hy, ⟨z, rfl⟩⟩
      have hyplane : inner Real v (D (f z)) = c := by
        obtain ⟨x, _, hx⟩ := hy
        change c • v + (A x : E3) = D (f z) at hx
        rw [← hx]
        simp [inner_add_right, inner_smul_right, hv,
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A x).property]
      have hDz : D (f z) = f z := hDplane _ ((hDheight _).symm.trans hyplane)
      have hz : f z ∈ f '' connectedComponentIn (h ⁻¹' {c}) p := by
        rw [← hintersection]
        exact ⟨hDz ▸ hy, mem_range_self z⟩
      obtain ⟨w, hw, hweq⟩ := hz
      refine ⟨w, hcenter.symm ▸ hw, ?_⟩
      exact congrArg D hweq
    · rintro ⟨z, ⟨q, rfl⟩, rfl⟩
      change D (f (F (q, 0))) ∈ _ ∩ range (fun p => D (f p))
      refine ⟨?_, mem_range_self _⟩
      rw [hDcenter]
      have hz : f (F (q, 0)) ∈ f '' connectedComponentIn (h ⁻¹' {c}) p :=
        ⟨F (q, 0), hcenter ▸ mem_range_self q, rfl⟩
      exact (hintersection.symm ▸ hz).1

theorem exists_prepared_innermost_regular_circle
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hne : (h ⁻¹' {c}).Nonempty) {R : Real} (hR : 0 < R) :
    ∃ p : S2, h p = c ∧ ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, inner Real v (D x) = inner Real v x) ∧
      (∀ x, inner Real v x = c -> D x = x) ∧
      (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - c| ≤ R} ∧
        ∀ x ∉ K, D x = x) ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p => D (f p)) ∧
      ∃ ε : Real, 0 < ε ∧ ε < R ∧
        ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
          T.source = univ ×ˢ Ioo (-ε) ε ∧
          ContMDiffOn Iprod (𝓡 2) ∞ T T.source ∧
          ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target ∧
          range (fun q : S1 => T (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p ∧
          ∃ γ : S1 -> Plane v,
            _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Plane v) ∞ γ ∧
            (∀ q t, t ∈ Ioo (-ε) ε ->
              D (f (T (q, t))) = (c + t) • v + (γ q : E3)) ∧
            ∃ A : Diffeomorph 𝓘(Real, Plane v) 𝓘(Real, Plane v) (Plane v) (Plane v) ∞,
              A '' sphere (0 : Plane v) 1 = range γ ∧
              ((fun x : Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
                range (fun p => D (f p)) =
                  (fun p => D (f p)) '' range (fun q : S1 => T (q, 0)) :=
  (fun _ => exists_prepared_innermost_regular_circle_of_smooth
    hf hh hv hheight c hc hne hR) hfinite

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
