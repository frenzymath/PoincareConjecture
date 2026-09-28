import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Critical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapHeight
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Caps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryCoreCap

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem exists_minimum_in_complement
    (D : SphereSurgeryCoreCap v g B)
    (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g) (hs : 0 < D.scale)
    (hreg : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ p : S2, p ∉ D.chart '' closedBall (0 : E2) 1 ∧
      inner Real v (g p) < D.center ∧
      IsMinOn (fun q => inner Real v (g q)) univ p ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p = 0 := by
  let h : S2 → Real := fun q => inner Real v (g q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h := (innerSL Real v).contMDiff.comp hg
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn univ_nonempty hh.continuous.continuousOn
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr
    (show (0 : Real) ≤ 1 by norm_num)
  have hboundary : h (D.chart x) = D.center := D.height_eq_on_boundary _ (mem_image_of_mem _ hx)
  have hlt : h p < D.center := by
    apply lt_of_le_of_ne (hboundary ▸ hp (mem_univ (D.chart x)))
    intro heq
    have hmin : IsMinOn h univ (D.chart x) := by
      intro y hy
      rw [hboundary, ← heq]
      exact hp hy
    exact hreg _ (mem_image_of_mem _ hx)
      (Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh
        (hmin.isLocalMin univ_mem))
  refine ⟨p, ?_, hlt, hp,
    Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh (hp.isLocalMin univ_mem)⟩
  rintro ⟨y, hy, hyp⟩
  have hnonneg := mul_nonneg (D.normalized_height_nonneg hy) hs.le
  rw [div_mul_cancel₀ _ D.scale_ne_zero] at hnonneg
  have heq : h p = inner Real v (D.parametrization y) := by
    rw [← hyp]
    exact congrArg (inner Real v) (D.parametrization_eq y hy)
  rw [heq] at hlt
  linarith

theorem exists_maximum_in_complement
    (D : SphereSurgeryCoreCap v g B)
    (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g) (hs : D.scale < 0)
    (hreg : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ p : S2, p ∉ D.chart '' closedBall (0 : E2) 1 ∧
      D.center < inner Real v (g p) ∧
      IsMaxOn (fun q => inner Real v (g q)) univ p ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p = 0 := by
  let h : S2 → Real := fun q => inner Real v (g q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h := (innerSL Real v).contMDiff.comp hg
  have hcrit {q : S2} (hq : IsLocalMax h q) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 := by
    have hn := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh.neg hq.neg
    change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) q = 0 at hn
    simpa only [mfderiv_neg, neg_eq_zero] using hn
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hh.continuous.continuousOn
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr
    (show (0 : Real) ≤ 1 by norm_num)
  have hboundary : h (D.chart x) = D.center := D.height_eq_on_boundary _ (mem_image_of_mem _ hx)
  have hlt : D.center < h p := by
    apply lt_of_le_of_ne (hboundary ▸ hp (mem_univ (D.chart x)))
    intro heq
    have hmax : IsMaxOn h univ (D.chart x) := by
      intro y hy
      rw [hboundary, heq]
      exact hp hy
    exact hreg _ (mem_image_of_mem _ hx) (hcrit (hmax.isLocalMax univ_mem))
  refine ⟨p, ?_, hlt, hp, hcrit (hp.isLocalMax univ_mem)⟩
  rintro ⟨y, hy, hyp⟩
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (D.normalized_height_nonneg hy) hs.le
  rw [div_mul_cancel₀ _ D.scale_ne_zero] at hnonpos
  have heq : h p = inner Real v (D.parametrization y) := by
    rw [← hyp]
    exact congrArg (inner Real v) (D.parametrization_eq y hy)
  rw [heq] at hlt
  linarith

end SphereSurgeryCoreCap

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)

private theorem regular_one_cap_boundary {g : S2 → E3}
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {B : Set Real} (D : SphereSurgeryCoreCap (M.v : E3) g B)
    (hcore : P.core = (D.chart '' ball (0 : E2) 1)ᶜ) :
    ∀ p ∈ D.chart '' sphere (0 : E2) 1, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p ≠ 0 := by
  have hfront : frontier P.core = D.chart '' sphere (0 : E2) 1 := by
    rw [hcore, frontier_compl, ParallelDisks.frontier_image_ball zero_lt_one D.chart
      D.source D.smooth D.symm_smooth]
  simpa only [hfront] using P.regular_on_frontier_core hP

theorem exists_minimum_chart_of_one_cap {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {B : Set Real} (D : SphereSurgeryCoreCap (M.v : E3) g B)
    (hcore : P.core = (D.chart '' ball (0 : E2) 1)ᶜ) (hs : 0 < D.scale) :
    ∃ p ∈ interior P.core,
      inner Real (M.v : E3) (g p) < D.center ∧
      IsMinOn (fun q => inner Real (M.v : E3) (g q)) univ p ∧
      (∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p) ∧
      ∃ e : OpenPartialHomeomorph E2 S2,
        0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        e.target ⊆ interior P.core ∧
        ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
          inner Real (M.v : E3) (g p) + ‖x‖ ^ 2 := by
  obtain ⟨p, hp, hpb, hmin, hc⟩ := D.exists_minimum_in_complement
    (M.tree.embedding_of_mem_leaves hg).contMDiff hs (M.regular_one_cap_boundary P hP D hcore)
  have hpK : p ∈ P.core := by
    rw [hcore]
    exact fun h => hp (image_mono ball_subset_closedBall h)
  have hpi := P.critical_mem_interior_core hP hpK hc
  obtain ⟨e, σ, hσ, he0, hep, he, hei, het, hform⟩ :=
    M.exists_morse_chart_in_core P hP hpK hc
  have hsign : ∀ i, σ i = 1 := morse_signs_eq_one_of_isLocalMin
    (h := fun q => inner Real (M.v : E3) (g q))
    e he0 σ hσ (by simpa only [hep] using hform)
      (by simpa only [hep] using hmin.isLocalMin univ_mem)
  refine ⟨p, hpi, hpb, hmin,
    fun q hq hqc => M.subsingleton_critical_core hg P ⟨hq, hqc⟩ ⟨hpK, hc⟩,
    e, he0, hep, he, hei, het, ?_⟩
  intro x hx
  simpa only [hsign, one_mul, ← EuclideanSpace.real_norm_sq_eq] using hform x hx

theorem exists_maximum_chart_of_one_cap {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {B : Set Real} (D : SphereSurgeryCoreCap (M.v : E3) g B)
    (hcore : P.core = (D.chart '' ball (0 : E2) 1)ᶜ) (hs : D.scale < 0) :
    ∃ p ∈ interior P.core,
      D.center < inner Real (M.v : E3) (g p) ∧
      IsMaxOn (fun q => inner Real (M.v : E3) (g q)) univ p ∧
      (∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p) ∧
      ∃ e : OpenPartialHomeomorph E2 S2,
        0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        e.target ⊆ interior P.core ∧
        ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
          inner Real (M.v : E3) (g p) - ‖x‖ ^ 2 := by
  obtain ⟨p, hp, hpb, hmax, hc⟩ := D.exists_maximum_in_complement
    (M.tree.embedding_of_mem_leaves hg).contMDiff hs (M.regular_one_cap_boundary P hP D hcore)
  have hpK : p ∈ P.core := by
    rw [hcore]
    exact fun h => hp (image_mono ball_subset_closedBall h)
  have hpi := P.critical_mem_interior_core hP hpK hc
  obtain ⟨e, σ, hσ, he0, hep, he, hei, het, hform⟩ :=
    M.exists_morse_chart_in_core P hP hpK hc
  have hnegform : ∀ x ∈ e.source, -inner Real (M.v : E3) (g (e x)) =
      -inner Real (M.v : E3) (g (e 0)) + ∑ i : Fin 2, (-σ i) * x i ^ 2 := by
    intro x hx
    rw [hform x hx, hep]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  have hsign : ∀ i, -σ i = 1 := morse_signs_eq_one_of_isLocalMin
    e he0 (fun i => -σ i) (fun i => by rcases hσ i with h | h <;> simp [h])
    hnegform (by simpa only [hep] using (hmax.isLocalMax univ_mem).neg)
  refine ⟨p, hpi, hpb, hmax,
    fun q hq hqc => M.subsingleton_critical_core hg P ⟨hq, hqc⟩ ⟨hpK, hc⟩,
    e, he0, hep, he, hei, het, ?_⟩
  intro x hx
  have h := hnegform x hx
  simp only [hsign, one_mul, ← EuclideanSpace.real_norm_sq_eq, hep] at h
  linarith

end SphereMorseReduction

end Poincare.Manifold.Schoenflies
