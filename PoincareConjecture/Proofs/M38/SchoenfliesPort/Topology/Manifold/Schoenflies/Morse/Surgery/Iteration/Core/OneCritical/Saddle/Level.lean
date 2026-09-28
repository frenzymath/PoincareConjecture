import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CapGap
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Critical
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary







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

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryCoreCap




theorem exists_physical_band_avoiding_caps
    {v : E3} {g : S2 → E3} {B : Set Real}
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    {c : Real} (hc : c ∈ B) :
    ∃ ε : Real, 0 < ε ∧
      (fun q => inner Real v (g q)) ⁻¹' Icc (c - ε) (c + ε) ⊆ interior C ∧
      ∀ D ∈ L, Disjoint (D.chart '' closedBall 0 1)
        ((fun q => inner Real v (g q)) ⁻¹' Icc (c - ε) (c + ε)) := by
  obtain ⟨ε, hε, hgap, _⟩ := exists_gap_around_protected_height L hc
  have hdisjoint (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) :
      Disjoint (D.chart '' closedBall 0 1)
        ((fun q => inner Real v (g q)) ⁻¹' Icc (c - ε) (c + ε)) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ hq
    have hbounds : inner Real v (D.parametrization x) ∈ Icc (c - ε) (c + ε) := by
      rwa [← D.parametrization_eq x hx]
    have habs : |inner Real v (D.parametrization x) - c| ≤ ε :=
      abs_le.mpr ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩
    exact (not_le_of_gt (hgap D hD x hx)) habs
  refine ⟨ε, hε, ?_, hdisjoint⟩
  intro q hq
  have hqC : q ∈ C := by
    rw [hcore]
    rintro hmem
    simp only [mem_iUnion] at hmem
    obtain ⟨D, hD, hqD⟩ := hmem
    exact Set.disjoint_left.mp (hdisjoint D hD) (image_mono ball_subset_closedBall hqD) hq
  apply (mem_interior_iff_notMem_frontier hqC).mpr
  intro hqfront
  rw [frontier_core L hpair hcore] at hqfront
  simp only [mem_iUnion] at hqfront
  obtain ⟨D, hD, hqD⟩ := hqfront
  exact Set.disjoint_left.mp (hdisjoint D hD) (image_mono sphere_subset_closedBall hqD) hq

end SphereSurgeryCoreCap

namespace SphereSurgeryPath



theorem exists_protected_physical_height_band
    {v : E3} {f g : S2 → E3} (P : SphereSurgeryPath v f g)
    (hcaps : P.PreservesCaps) {B : Set Real} (hP : P.Protects B)
    {c : Real} (hc : c ∈ B) :
    ∃ ε : Real, 0 < ε ∧
      (fun q => inner Real v (g q)) ⁻¹' Icc (c - ε) (c + ε) ⊆ interior P.core := by
  obtain ⟨L, hpair, hcore⟩ := P.exists_model_cap_complement hcaps hP
  obtain ⟨ε, hε, hband, _⟩ :=
    SphereSurgeryCoreCap.exists_physical_band_avoiding_caps L hpair hcore hc
  exact ⟨ε, hε, hband⟩

end SphereSurgeryPath

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)

include hg hP hcaps hp hc




theorem exists_physical_band_with_unique_critical_point :
    ∃ ε : Real, 0 < ε ∧
      (fun q => inner Real (M.v : E3) (g q)) ⁻¹'
        Icc (inner Real (M.v : E3) (g p) - ε) (inner Real (M.v : E3) (g p) + ε) ⊆
          interior P.core ∧
      {q | inner Real (M.v : E3) (g q) ∈
          Icc (inner Real (M.v : E3) (g p) - ε) (inner Real (M.v : E3) (g p) + ε) ∧
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real (M.v : E3) (g y)) q = 0} = {p} := by
  have hprotected : inner Real (M.v : E3) (g p) ∈
      ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}) :=
    ⟨p, (P.mfderiv_eq_on_core p hp).symm.trans hc, (P.height_eq_on_core hp).symm⟩
  obtain ⟨ε, hε, hband⟩ := P.exists_protected_physical_height_band hcaps hP hprotected
  refine ⟨ε, hε, hband, ?_⟩
  ext q
  constructor
  · rintro ⟨hqband, hqcrit⟩
    exact mem_singleton_iff.mpr ((M.subsingleton_critical_core hg P)
      ⟨interior_subset (hband hqband), hqcrit⟩ ⟨hp, hc⟩)
  · rintro rfl
    exact ⟨⟨by linarith, by linarith⟩, hc⟩

theorem physical_critical_level_subset_interior_core :
    {q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} ⊆ interior P.core := by
  obtain ⟨ε, hε, hband, _⟩ := M.exists_physical_band_with_unique_critical_point hg P hP hcaps hp hc
  intro q hq
  apply hband
  change inner Real (M.v : E3) (g q) ∈ Icc _ _
  rw [hq]
  exact ⟨by linarith, by linarith⟩

theorem eq_of_physical_critical_level
    {q : S2} (hqheight : inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p))
    (hqcrit : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0) : q = p :=
  (M.subsingleton_critical_core hg P)
    ⟨interior_subset (M.physical_critical_level_subset_interior_core hg P hP hcaps hp hc hqheight),
      hqcrit⟩ ⟨hp, hc⟩

theorem physical_critical_level_regular_away
    {q : S2} (hqheight : inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p))
    (hqne : q ≠ p) : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q ≠ 0 :=
  fun hqcrit => hqne (M.eq_of_physical_critical_level hg P hP hcaps hp hc hqheight hqcrit)

end SphereMorseReduction

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
