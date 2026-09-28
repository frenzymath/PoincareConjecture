import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalHeight
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.TimeClamp

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
local notation "Itime" => ModelWithCorners.prod 𝓘(Real, Real) (𝓡 1)

theorem Saddle.Caps.exists_jointly_injective_chart_slices
    {ι : Type*} [Finite ι] (T : ι → OpenPartialHomeomorph (S1 × Real) S2)
    {c : Real} (hs : ∀ i q, (q, c) ∈ (T i).source)
    (hinj : Injective (fun z : ι × S1 => T z.1 (z.2, c))) :
    ∃ ε : Real, 0 < ε ∧
      (∀ i, univ ×ˢ Icc (c - ε) (c + ε) ⊆ (T i).source) ∧
      ∀ t ∈ Icc (c - ε) (c + ε), Injective (fun z : ι × S1 => T z.1 (z.2, t)) := by
  have hsource (i : ι) : ∀ᶠ t in 𝓝 c, ∀ q : S1, (q, t) ∈ (T i).source := by
    have hh := (isCompact_univ : IsCompact (univ : Set S1)).eventually_forall_of_forall_eventually
      (x₀ := c) (P := fun t q => (q, t) ∈ (T i).source) (by
        intro q _
        exact continuous_swap.continuousAt.preimage_mem_nhds
          ((T i).open_source.mem_nhds (hs i q)))
    simpa only [mem_univ, forall_const] using hh
  have hpair (i j : ι) : ∀ᶠ t in 𝓝 c, i ≠ j → ∀ q r : S1, T i (q, t) ≠ T j (r, t) := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ hne => False.elim (hne hij))
    have hh :=
      (isCompact_univ : IsCompact (univ : Set (S1 × S1))).eventually_forall_of_forall_eventually
      (x₀ := c) (P := fun t qr => T i (qr.1, t) ≠ T j (qr.2, t)) (by
        rintro ⟨q, r⟩ _
        have hi : ContinuousAt (fun z : Real × (S1 × S1) => T i (z.2.1, z.1)) (c, (q, r)) :=
          ((T i).continuousAt (hs i q)).comp
            (f := fun z : Real × (S1 × S1) => (z.2.1, z.1)) (by fun_prop)
        have hj : ContinuousAt (fun z : Real × (S1 × S1) => T j (z.2.2, z.1)) (c, (q, r)) :=
          ((T j).continuousAt (hs j r)).comp
            (f := fun z : Real × (S1 × S1) => (z.2.2, z.1)) (by fun_prop)
        apply (hi.ne_iff_eventually_ne hj).mp
        intro heq
        exact hij (congrArg Prod.fst (@hinj (i, q) (j, r) heq)))
    filter_upwards [hh] with t ht _ q r
    exact ht (q, r) (mem_univ _)
  have hnear : ∀ᶠ t in 𝓝 c,
      (∀ i q, (q, t) ∈ (T i).source) ∧
      (∀ i j, i ≠ j → ∀ q r : S1, T i (q, t) ≠ T j (r, t)) :=
    (eventually_all.mpr hsource).and
      (eventually_all.mpr (fun i => eventually_all.mpr (hpair i)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall {t : Real} (ht : t ∈ Icc (c - δ / 2) (c + δ / 2)) : t ∈ ball c δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
  · rintro i ⟨q, t⟩ ⟨_, ht⟩
    exact (hδsub (hsmall ht)).1 i q
  · intro t ht
    rintro ⟨i, q⟩ ⟨j, r⟩ heq
    have h := hδsub (hsmall ht)
    have hij : i = j := by
      by_contra hne
      exact h.2 i j hne q r heq
    subst j
    exact Prod.ext rfl (congrArg Prod.fst ((T i).injOn (h.1 i q) (h.1 i r) heq))

open SphereSurgeryCoreCap.AnnularEndFamily

theorem Saddle.Caps.exists_projected_terminal_slice_family
    {ι : Type*} [Finite ι] {v : E3} (hv : ‖v‖ = 1) {g : S2 → E3}
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (T : ι → OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ∀ i, ContMDiffOn Iprod (𝓡 2) ∞ (T i) (T i).source)
    (hTi : ∀ i, ContMDiffOn (𝓡 2) Iprod ∞ (T i).symm (T i).target)
    (c : Real)
    (hphysical : ∀ i, ∃ ε : Real, 0 < ε ∧
      univ ×ˢ Icc (c - ε) (c + ε) ⊆ (T i).source ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) → inner Real v (g (T i (q, t))) = t)
    (hinj : Injective (fun z : ι × S1 => T z.1 (z.2, c))) :
    ∃ r : Real, 0 < r ∧ ∃ γ : ι → Real × S1 → (Real ∙ v)ᗮ,
      (∀ i, ContMDiff Itime 𝓘(Real, (Real ∙ v)ᗮ) ∞ (γ i)) ∧
      (∀ i t, t ∈ Icc (-r) r → ∀ q,
        γ i (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (T i (q, c + t)))) ∧
      (∀ i t, t ∈ Icc (-r) r → ∀ q, inner Real v (g (T i (q, c + t))) = c + t) ∧
      (∀ i t, _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
        (fun q : S1 => γ i (t, q))) ∧
      ∀ t, Injective (fun z : ι × S1 => γ z.1 (t, z.2)) := by
  have hs (i : ι) (q : S1) : (q, c) ∈ (T i).source := by
    obtain ⟨ε, hε, hsource, _⟩ := hphysical i
    exact hsource ⟨mem_univ _, by constructor <;> linarith⟩
  obtain ⟨η, hη, _, hjoint⟩ := Saddle.Caps.exists_jointly_injective_chart_slices T hs hinj
  have hnear (i : ι) : ∀ᶠ t in 𝓝 c, ∀ q,
      (q, t) ∈ (T i).source ∧ inner Real v (g (T i (q, t))) = t := by
    obtain ⟨ε, hε, hsource, hheight⟩ := hphysical i
    filter_upwards [Icc_mem_nhds (by linarith : c - ε < c) (by linarith : c < c + ε)]
      with t ht q
    exact ⟨hsource ⟨mem_univ _, ht⟩, hheight q t ht⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (eventually_all.mpr hnear)
  let s := min η (δ / 2)
  have hspos : 0 < s := lt_min hη (half_pos hδ)
  have hsη : s ≤ η := min_le_left _ _
  have hsδ : s ≤ δ / 2 := min_le_right _ _
  have hdata {t : Real} (ht : t ∈ Icc (c - s) (c + s)) (i : ι) (q : S1) :
      (q, t) ∈ (T i).source ∧ inner Real v (g (T i (q, t))) = t := by
    apply hδsub _ i q
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hjoint' {t : Real} (ht : t ∈ Icc (c - s) (c + s)) :
      Injective (fun z : ι × S1 => T z.1 (z.2, t)) :=
    hjoint t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨κ, hκ, hκrange, _, _, hκpieces⟩ := exists_smooth_band_endpoint_clamp
    (a := -s) (b := s) (w := s / 4) (by positivity) (by linarith)
  have hκid {t : Real} (ht : t ∈ Icc (-(s / 2)) (s / 2)) : κ t = t := by
    rcases hκpieces t ⟨by linarith [ht.1], by linarith [ht.2]⟩ with hl | hr | heq
    · linarith [hl.1.2, ht.1]
    · linarith [hr.1.1, ht.2]
    · exact heq
  have hctime (t : Real) : c + κ t ∈ Icc (c - s) (c + s) := by
    constructor <;> linarith [(hκrange t).1, (hκrange t).2]
  let γ : ι → Real × S1 → (Real ∙ v)ᗮ := fun i z =>
    (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (T i (z.2, c + κ z.1)))
  refine ⟨s / 2, half_pos hspos, γ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hmap : ContMDiff Itime Iprod ∞ (fun z : Real × S1 => (z.2, c + κ z.1)) :=
      contMDiff_snd.prodMk (contMDiff_const.add (hκ.contMDiff.comp contMDiff_fst))
    have hchart : ContMDiff Itime (𝓡 2) ∞ (fun z : Real × S1 => T i (z.2, c + κ z.1)) := by
      intro z
      exact ((hT i).contMDiffAt ((T i).open_source.mem_nhds
        (hdata (hctime z.1) i z.2).1)).comp z (hmap z)
    exact (Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp (hg.contMDiff.comp hchart)
  · intro i t ht q
    dsimp only [γ]
    rw [hκid ht]
  · intro i t ht q
    exact (hdata (by constructor <;> linarith [ht.1, ht.2]) i q).2
  · intro i t
    obtain ⟨hcircle, hcircleinj, hcircleder⟩ := annular_slice_geometry (T i) (hT i) (hTi i)
      (c + κ t) (fun q => (hdata (hctime t) i q).1)
    exact projected_circle_embedding hg hv _ hcircle hcircleinj hcircleder
      (fun q => (hdata (hctime t) i q).2)
  · intro t z y heq
    apply hjoint' (hctime t)
    apply hg.isEmbedding.injective
    apply (Poincare.Geometry.Euclidean.heightCoordinates hv).symm.injective
    exact Prod.ext ((hdata (hctime t) z.1 z.2).2.trans
      (hdata (hctime t) y.1 y.2).2.symm) heq

namespace SphereSurgeryCoreCap.AnnularEndFamily

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

theorem exists_lower_terminal_projected_slice_family
    (ends : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1) :
    ∃ r : Real, 0 < r ∧ ∃ γ : ends.LowerCutIndex → Real × S1 → (Real ∙ v)ᗮ,
      (∀ i, ContMDiff Itime 𝓘(Real, (Real ∙ v)ᗮ) ∞ (γ i)) ∧
      (∀ i t, t ∈ Icc (-r) r → ∀ q,
        γ i (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto
          (g ((ends.lower i.1.1 i.1.2 i.2).chart (q, ends.lowerCut + t)))) ∧
      (∀ (i : ends.LowerCutIndex) t, t ∈ Icc (-r) r → ∀ q,
        inner Real v (g ((ends.lower i.1.1 i.1.2 i.2).chart (q, ends.lowerCut + t))) =
          ends.lowerCut + t) ∧
      (∀ i t, _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
        (fun q : S1 => γ i (t, q))) ∧
      ∀ t, Injective (fun z : ends.LowerCutIndex × S1 => γ z.1 (t, z.2)) := by
  exact Saddle.Caps.exists_projected_terminal_slice_family hv hg
    (fun i : ends.LowerCutIndex => (ends.lower i.1.1 i.1.2 i.2).chart)
    (fun i => (ends.lower i.1.1 i.1.2 i.2).smooth)
    (fun i => (ends.lower i.1.1 i.1.2 i.2).symm_smooth) ends.lowerCut
    (fun i => ends.exists_lower_terminal_physical_height i.1.1 i.1.2 i.2)
    ends.lowerCutCircle_joint_injective

theorem exists_upper_terminal_projected_slice_family
    (ends : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1) :
    ∃ r : Real, 0 < r ∧ ∃ γ : ends.UpperCutIndex → Real × S1 → (Real ∙ v)ᗮ,
      (∀ i, ContMDiff Itime 𝓘(Real, (Real ∙ v)ᗮ) ∞ (γ i)) ∧
      (∀ i t, t ∈ Icc (-r) r → ∀ q,
        γ i (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto
          (g ((ends.upper i.1.1 i.1.2 i.2).chart (q, ends.upperCut + t)))) ∧
      (∀ (i : ends.UpperCutIndex) t, t ∈ Icc (-r) r → ∀ q,
        inner Real v (g ((ends.upper i.1.1 i.1.2 i.2).chart (q, ends.upperCut + t))) =
          ends.upperCut + t) ∧
      (∀ i t, _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
        (fun q : S1 => γ i (t, q))) ∧
      ∀ t, Injective (fun z : ends.UpperCutIndex × S1 => γ z.1 (t, z.2)) := by
  exact Saddle.Caps.exists_projected_terminal_slice_family hv hg
    (fun i : ends.UpperCutIndex => (ends.upper i.1.1 i.1.2 i.2).chart)
    (fun i => (ends.upper i.1.1 i.1.2 i.2).smooth)
    (fun i => (ends.upper i.1.1 i.1.2 i.2).symm_smooth) ends.upperCut
    (fun i => ends.exists_upper_terminal_physical_height i.1.1 i.1.2 i.2)
    ends.upperCutCircle_joint_injective

end SphereSurgeryCoreCap.AnnularEndFamily
end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
