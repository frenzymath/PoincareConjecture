import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalSlices
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Family.Cylinder

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem Saddle.Caps.exists_terminal_cylinder_straightening
    {ι : Type*} [Finite ι] {v : E3} (hv : ‖v‖ = 1) {g : S2 → E3}
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (T : ι → OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ∀ i, ContMDiffOn Iprod (𝓡 2) ∞ (T i) (T i).source)
    (hTi : ∀ i, ContMDiffOn (𝓡 2) Iprod ∞ (T i).symm (T i).target)
    (c : Real)
    (hphysical : ∀ i, ∃ ε : Real, 0 < ε ∧
      univ ×ˢ Icc (c - ε) (c + ε) ⊆ (T i).source ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) → inner Real v (g (T i (q, t))) = t)
    (hinj : Injective (fun z : ι × S1 => T z.1 (z.2, c)))
    {R : Real} (hR : 0 < R) :
    ∃ r : Real, 0 < r ∧ r < R ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (G x) = inner Real v x) ∧
        (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - c| ≤ R} ∧
          ∀ x ∉ K, G x = x) ∧
        EqOn G id {x | inner Real v x = c} ∧
        ∀ i t, t ∈ Icc (-r) r → ∀ q,
          G (g (T i (q, c + t))) = g (T i (q, c)) + t • v := by
  obtain ⟨r₀, hr₀, γ, hγ, hprojection, hheight, hemb, hjoint⟩ :=
    Saddle.Caps.exists_projected_terminal_slice_family hv hg T hT hTi c hphysical hinj
  let r := min r₀ (R / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hR)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrR : r < R := (min_le_right r₀ (R / 2)).trans_lt (by linarith)
  have hinterval {t : Real} (ht : t ∈ Icc (-r) r) : t ∈ Icc (-r₀) r₀ :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hzero : (0 : Real) ∈ Icc (-r₀) r₀ := ⟨by linarith, hr₀.le⟩
  obtain ⟨F, hFheight, ⟨K, hK, hKslab, hfix⟩, hcentral, hF⟩ :=
    exists_supported_ambient_cylinder_family_within hv c hr hrR γ hγ
      (fun i t _ => hemb i t) (fun t _ => hjoint t)
  refine ⟨r, hr, hrR, F.symm, ?_, ⟨K, hK, hKslab, ?_⟩, ?_, ?_⟩
  · intro x
    have hh := hFheight (F.symm x)
    rw [F.apply_symm_apply] at hh
    exact hh.symm
  · intro x hx
    apply F.injective
    change F (F.symm x) = F x
    rw [F.apply_symm_apply, hfix x hx]
  · intro x hx
    apply F.injective
    change F (F.symm x) = F x
    rw [F.apply_symm_apply, hcentral hx]
    rfl
  · intro i t ht q
    apply F.injective
    change F (F.symm (g (T i (q, c + t)))) = F (g (T i (q, c)) + t • v)
    rw [F.apply_symm_apply]
    have hstart : g (T i (q, c)) = c • v + (γ i (0, q) : E3) := by
      have hh := (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply
        (g (T i (q, c)))
      change inner Real v (g (T i (q, c))) • v +
        ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g (T i (q, c))) : E3) = _ at hh
      have hph := hprojection i 0 hzero q
      have hht := hheight i 0 hzero q
      simp only [add_zero] at hph hht
      rw [hht, ← hph] at hh
      exact hh.symm
    have hend : (c + t) • v + (γ i (t, q) : E3) = g (T i (q, c + t)) := by
      have hh := (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply
        (g (T i (q, c + t)))
      change inner Real v (g (T i (q, c + t))) • v +
        ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g (T i (q, c + t))) : E3) = _ at hh
      rw [hheight i t (hinterval ht) q, ← hprojection i t (hinterval ht) q] at hh
      exact hh
    have hsum : g (T i (q, c)) + t • v = (c + t) • v + (γ i (0, q) : E3) := by
      rw [hstart, add_smul]
      abel
    rw [hsum, hF i t ht q, hend]

namespace SphereSurgeryCoreCap.AnnularEndFamily

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

theorem exists_lower_terminal_cylinder_straightening
    (ends : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    {R : Real} (hR : 0 < R) :
    ∃ r : Real, 0 < r ∧ r < R ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (G x) = inner Real v x) ∧
        (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - ends.lowerCut| ≤ R} ∧
          ∀ x ∉ K, G x = x) ∧
        EqOn G id {x | inner Real v x = ends.lowerCut} ∧
        ∀ (i : ends.LowerCutIndex) t, t ∈ Icc (-r) r → ∀ q,
          G (g ((ends.lower i.1.1 i.1.2 i.2).chart (q, ends.lowerCut + t))) =
            g ((ends.lower i.1.1 i.1.2 i.2).chart (q, ends.lowerCut)) + t • v := by
  exact Saddle.Caps.exists_terminal_cylinder_straightening hv hg
    (fun i : ends.LowerCutIndex => (ends.lower i.1.1 i.1.2 i.2).chart)
    (fun i => (ends.lower i.1.1 i.1.2 i.2).smooth)
    (fun i => (ends.lower i.1.1 i.1.2 i.2).symm_smooth) ends.lowerCut
    (fun i => ends.exists_lower_terminal_physical_height i.1.1 i.1.2 i.2)
    ends.lowerCutCircle_joint_injective hR

theorem exists_upper_terminal_cylinder_straightening
    (ends : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    {R : Real} (hR : 0 < R) :
    ∃ r : Real, 0 < r ∧ r < R ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (G x) = inner Real v x) ∧
        (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - ends.upperCut| ≤ R} ∧
          ∀ x ∉ K, G x = x) ∧
        EqOn G id {x | inner Real v x = ends.upperCut} ∧
        ∀ (i : ends.UpperCutIndex) t, t ∈ Icc (-r) r → ∀ q,
          G (g ((ends.upper i.1.1 i.1.2 i.2).chart (q, ends.upperCut + t))) =
            g ((ends.upper i.1.1 i.1.2 i.2).chart (q, ends.upperCut)) + t • v := by
  exact Saddle.Caps.exists_terminal_cylinder_straightening hv hg
    (fun i : ends.UpperCutIndex => (ends.upper i.1.1 i.1.2 i.2).chart)
    (fun i => (ends.upper i.1.1 i.1.2 i.2).smooth)
    (fun i => (ends.upper i.1.1 i.1.2 i.2).symm_smooth) ends.upperCut
    (fun i => ends.exists_upper_terminal_physical_height i.1.1 i.1.2 i.2)
    ends.upperCutCircle_joint_injective hR

end SphereSurgeryCoreCap.AnnularEndFamily
end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
