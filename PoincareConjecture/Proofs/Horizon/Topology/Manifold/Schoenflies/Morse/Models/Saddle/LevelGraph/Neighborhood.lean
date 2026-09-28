import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Exterior
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Isolation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.ContactGerms

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_saddle_level_exterior
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2) :
    ∃ (r : Real) (O : Set S2), 0 < r ∧ closedSquare r ⊆ e.source ∧ IsOpen O ∧
      let L := h ⁻¹' {h p}
      let C := connectedComponentIn L p
      let K := C \ e '' openSquare r
      let b : Fin 2 × Fin 2 → S2 := fun i => e (contact r i)
      C ⊆ O ∧ O ∩ L = C ∧ Function.Injective b ∧
      K ∩ e '' closedSquare r = range b ∧ IsCompact K ∧
      (∃ U : Opens S2, K ⊆ U ∧
        ∀ q ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0) ∧
      (∀ q ∈ K \ range b, ∃ W : Set S2, IsOpen W ∧ q ∈ W ∧ W ∩ L ⊆ K) ∧
      (∀ i : Fin 2 × Fin 2, ∃ δ : Real, 0 < δ ∧ δ < 1 ∧
        ∃ W : Set S2, IsOpen W ∧ b i ∈ W ∧
          let γ : Real → S2 := fun t => e ((1 + t) • contact r i)
          ContMDiffOn 𝓘(Real, Real) (𝓡 2) ∞ γ (Ioo (-δ) δ) ∧
          InjOn γ (Ioo (-δ) δ) ∧ W ∩ L = γ '' Ioo (-δ) δ ∧
          (∀ t ∈ Ioo (-δ) δ, e.symm (γ t) 0 / contact r i 0 - 1 = t) ∧
          ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
            (fun q => e.symm q 0 / contact r i 0 - 1) W ∧
          ∀ t ∈ Ioo (-δ) δ, γ t ∈ K ↔ 0 ≤ t) ∧
      (∀ q ∈ K, ∃ i : Fin 2 × Fin 2, b i ∈ connectedComponentIn K q) ∧
      Finite (ConnectedComponents K) := by
  obtain ⟨r, hr, hrs, hinj, hcontacts, hcompact, hregular, hattach, hfinite⟩ :=
    exists_compact_regular_exterior hh hunique e he0 hep hform
  obtain ⟨O, hO, hCO, hlevel⟩ := exists_open_isolating_neighborhood hh hunique e he0 hep hform
  let C := connectedComponentIn (h ⁻¹' {h p}) p
  let K := C \ e '' openSquare r
  have hclosed : IsClosed (e '' closedSquare r) :=
    ((isCompact_closedSquare hr.le).image_of_continuousOn (e.continuousOn.mono hrs)).isClosed
  refine ⟨r, O, hr, hrs, hO, hCO, hlevel, hinj, hcontacts, hcompact,
    ?_, ?_, ?_, hattach, hfinite⟩
  · refine ⟨⟨{q | mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0},
      (Poincare.Geometry.Manifold.isClosed_setOf_mfderiv_eq_zero
        (hh.of_le (by simp))).isOpen_compl⟩, hregular, fun _ hq => hq⟩
  · intro q hq
    have hqout : q ∉ e '' closedSquare r := by
      intro hqpatch
      exact hq.2 (hcontacts ▸ (show q ∈ K ∩ e '' closedSquare r from ⟨hq.1, hqpatch⟩))
    refine ⟨O \ e '' closedSquare r, hO.inter hclosed.isOpen_compl,
      ⟨hCO hq.1.1, hqout⟩, ?_⟩
    rintro y ⟨⟨hyO, hyout⟩, hyL⟩
    refine ⟨hlevel ▸ (show y ∈ O ∩ h ⁻¹' {h p} from ⟨hyO, hyL⟩), ?_⟩
    exact fun hy => hyout (image_mono (openSquare_subset_closedSquare r) hy)
  · intro i
    simpa only [hep] using exists_contact_halfInterval e he hei hr hrs hform i

theorem unique_on_level_of_unique_in_band
    {h : S2 → Real} {p : S2} {a b : Real} (hp : h p ∈ Icc a b)
    (hcritical : {q | h q ∈ Icc a b ∧ mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0} = {p}) :
    ∀ q, h q = h p → mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p := by
  intro q hq hqc
  have : q ∈ {r | h r ∈ Icc a b ∧ mfderiv (𝓡 2) 𝓘(Real, Real) h r = 0} :=
    ⟨hq ▸ hp, hqc⟩
  rwa [hcritical] at this

end Poincare.Manifold.Schoenflies.SaddleLevel
