import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.PlanarTube
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.SpatialLocalizedCylinder

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩
private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real

theorem exists_supported_ambient_regular_level_flattening_within_of_smooth
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c)
    {U : Set (Real ∙ v)ᗮ} (hU : IsOpen U)
    (hCU : (fun x => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f x)) ''
      connectedComponentIn (h ⁻¹' {c}) p ⊆ U)
    {R : Real} (hR : 0 < R) :
    ∃ ε : Real, 0 < ε ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t) ∧
      range (fun q : S1 => F (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p ∧
      ∃ r : Real, 0 < r ∧ r < ε ∧ r < R ∧ ∃ K : Set E3,
        IsCompact K ∧ K ⊆ {x | |inner Real v x - c| ≤ R ∧
          (Real ∙ v)ᗮ.orthogonalProjectionOnto x ∈ U} ∧
        ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ x, inner Real v (D x) = inner Real v x) ∧
          (∀ x, inner Real v x = c -> D x = x) ∧
          (∀ x ∉ K, D x = x) ∧
          ∀ t ∈ Icc (-r) r, ∀ q, D (f (F (q, t))) = f (F (q, 0)) + t • v := by
  obtain ⟨ε, hε, F, hsource, hF, hFinv, hlevel, hcentral,
    s, hs, hsε, γ, hγ, hemb, hγrange, hlift⟩ :=
    exists_smooth_planar_family_of_regular_level_component_of_smooth hf hh hv hheight c hc p hp
  have hzero : ({0} : Set Real) ×ˢ (univ : Set S1) ⊆ γ ⁻¹' U := by
    rintro ⟨t, q⟩ ⟨ht, _⟩
    have ht0 : t = 0 := ht
    subst t
    exact hCU (hγrange ▸ mem_range_self q)
  obtain ⟨V, W, hV, _, h0V, hSW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ
      (hU.preimage hγ.continuous) hzero
  obtain ⟨d, hd, hdV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (by simp))
  let r := min s (min R d) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < s := by
    have := min_le_left s (min R d)
    dsimp [r] at *
    linarith
  have hrR : r < R := by
    have := (min_le_right s (min R d)).trans (min_le_left R d)
    dsimp [r] at *
    linarith
  have hrd : r < d := by
    have := (min_le_right s (min R d)).trans (min_le_right R d)
    dsimp [r] at *
    linarith
  have hsmall (t : Real) (ht : t ∈ Icc (-r) r) : t ∈ Icc (-s) s :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htrace (t : Real) (ht : t ∈ Icc (-r) r) (q : S1) : γ (t, q) ∈ U := by
    apply hVW
    refine ⟨hdV ?_, hSW (mem_univ q)⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero] using (abs_le.mpr ht).trans_lt hrd
  obtain ⟨K, hK, hKU, H, hHheight, hHzero, hHfix, hHmotion⟩ :=
    exists_supported_ambient_cylinder_within hv c hr hrR hU γ hγ
      (fun t _ => hemb t) htrace
  have hzeroγ (q : S1) : f (F (q, 0)) = c • v + (γ (0, q) : E3) := by
    simpa only [add_zero] using (hlift 0 ⟨by linarith, hs.le⟩ q).2
  refine ⟨ε, hε, F, hsource, hF, hFinv, hlevel, hcentral,
    r, hr, hrs.trans hsε, hrR, K, hK, hKU, H.symm, ?_, ?_, ?_, ?_⟩
  · intro x
    have heq := hHheight (H.symm x)
    rw [H.apply_symm_apply] at heq
    exact heq.symm
  · intro x hx
    apply H.injective
    change H (H.symm x) = H x
    rw [H.apply_symm_apply, hHzero x hx]
  · intro x hx
    apply H.injective
    change H (H.symm x) = H x
    rw [H.apply_symm_apply, hHfix x hx]
  · intro t ht q
    rw [(hlift t (hsmall t ht) q).2, ← hHmotion t ht q,
      H.symm_apply_apply, hzeroγ, add_smul]
    abel

theorem exists_supported_ambient_regular_level_flattening_within
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c)
    {U : Set (Real ∙ v)ᗮ} (hU : IsOpen U)
    (hCU : (fun x => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f x)) ''
      connectedComponentIn (h ⁻¹' {c}) p ⊆ U)
    {R : Real} (hR : 0 < R) :
    ∃ ε : Real, 0 < ε ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t) ∧
      range (fun q : S1 => F (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p ∧
      ∃ r : Real, 0 < r ∧ r < ε ∧ r < R ∧ ∃ K : Set E3,
        IsCompact K ∧ K ⊆ {x | |inner Real v x - c| ≤ R ∧
          (Real ∙ v)ᗮ.orthogonalProjectionOnto x ∈ U} ∧
        ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ x, inner Real v (D x) = inner Real v x) ∧
          (∀ x, inner Real v x = c -> D x = x) ∧
          (∀ x ∉ K, D x = x) ∧
          ∀ t ∈ Icc (-r) r, ∀ q, D (f (F (q, t))) = f (F (q, 0)) + t • v :=
  (fun _ => exists_supported_ambient_regular_level_flattening_within_of_smooth
    hf hh hv hheight c hc p hp hU hCU hR) hfinite

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
