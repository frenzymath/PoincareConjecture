import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Perturbation.Graph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Critical
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_regularization_of_morse_level
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 → Real) (hσ : ∀ i, σ i ≠ 0)
    (hform : ∀ x ∈ e.source, h (e x) = h p + ∑ i, σ i * x i ^ 2)
    {R : Real} (hR : 0 < R) (hRs : closedBall (0 : E2) R ⊆ e.source) :
    ∃ H : S2 → Real, ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H ∧
      (∀ q, mfderiv (𝓡 2) 𝓘(Real, Real) H q = 0 ↔
        mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0) ∧
      H p ≠ h p ∧
      (∀ q, mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q ≠ p → H q = h q) ∧
      (∀ q ∉ e '' closedBall (0 : E2) R, H =ᶠ[𝓝 q] h) ∧
      ∀ q, H q = h p → mfderiv (𝓡 2) 𝓘(Real, Real) H q ≠ 0 := by
  classical
  let Q : E2 → Real := fun x => h p + ∑ i, σ i * x i ^ 2
  have hQ := Poincare.Analysis.Calculus.Morse.contDiff_diagonal_quadratic (h p) σ
  have hQc (x : E2) : fderiv Real Q x = 0 ↔ x = 0 :=
    Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff (h p) σ hσ x
  obtain ⟨g, t, hg, _, hgc, _, hgo, hg0⟩ :=
    exists_bump_shift_avoiding_finite_heights hQ (0 : E2)
      (half_pos hR) (half_lt_self hR) (by norm_num : (0 : Real) < 1)
      (fun x hx hz => hx.2 ((hQc x).mp hz ▸ mem_ball_self (half_pos hR)))
      (finite_singleton (h p))
  let H : S2 → Real := fun q => if q ∈ e.target then g (e.symm q) else h q
  have hHe (x : E2) (hx : x ∈ e.source) : H (e x) = g x := by
    simp only [H, if_pos (e.map_source hx), e.left_inv hx]
  have hout : ∀ q ∉ e '' closedBall (0 : E2) R, H =ᶠ[𝓝 q] h := by
    intro q hq
    have hclosed : IsClosed (e '' closedBall (0 : E2) R) :=
      ((isCompact_closedBall 0 R).image_of_continuousOn (e.continuousOn.mono hRs)).isClosed
    filter_upwards [hclosed.isOpen_compl.mem_nhds hq] with y hy
    by_cases hyt : y ∈ e.target
    · have hys := e.map_target hyt
      have hyR : e.symm y ∉ closedBall (0 : E2) R :=
        fun hyR => hy ⟨e.symm y, hyR, e.right_inv hyt⟩
      rw [show H y = g (e.symm y) from if_pos hyt, hgo hyR]
      exact (hform (e.symm y) hys).symm.trans (congrArg h (e.right_inv hyt))
    · exact if_neg hyt
  have hH : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H := by
    intro q
    by_cases hqt : q ∈ e.target
    · have hl := hg.contMDiff.contMDiffAt.comp q
        ((hei q hqt).contMDiffAt (e.open_target.mem_nhds hqt))
      apply hl.congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hqt] with y hy
      exact if_pos hy
    · have hqo : q ∉ e '' closedBall (0 : E2) R := by
        rintro ⟨x, hx, rfl⟩
        exact hqt (e.map_source (hRs hx))
      exact (hh q).congr_of_eventuallyEq (hout q hqo)
  have hcrit (q : S2) : mfderiv (𝓡 2) 𝓘(Real, Real) H q = 0 ↔
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 := by
    by_cases hqt : q ∈ e.target
    · have hqs := e.map_target hqt
      rw [← e.right_inv hqt,
        mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eqOn hH e he hei hqs hHe,
        mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eqOn hh e he hei hqs hform]
      exact hgc _
    · have hqo : q ∉ e '' closedBall (0 : E2) R := by
        rintro ⟨x, hx, rfl⟩
        exact hqt (e.map_source (hRs hx))
      rw [(hout q hqo).mfderiv_eq]
  have hpchange : H p ≠ h p := by
    rw [← hep, hHe 0 he0]
    simpa only [mem_singleton_iff, hep] using hg0
  have hvalues (q : S2) (hqc : mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0)
      (hqp : q ≠ p) : H q = h q := by
    by_cases hqt : q ∈ e.target
    · have hzero : mfderiv (𝓡 2) 𝓘(Real, Real) h (e (e.symm q)) = 0 := by
        rw [e.right_inv hqt]
        exact hqc
      have hz : e.symm q = 0 := (hQc _).mp
        ((mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eqOn hh e he hei
          (e.map_target hqt) hform).mp hzero)
      exact (hqp ((e.right_inv hqt).symm.trans ((congrArg e hz).trans hep))).elim
    · exact if_neg hqt
  refine ⟨H, hH, hcrit, hpchange, hvalues, hout, ?_⟩
  intro q hq hqc
  have hqc' := (hcrit q).mp hqc
  by_cases hqp : q = p
  · exact hpchange (hqp ▸ hq)
  · exact hqp (hunique q ((hvalues q hqc' hqp).symm.trans hq) hqc')

theorem exists_compact_regular_completion_of_morse_exterior
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 → Real) (hσ : ∀ i, σ i ≠ 0)
    (hform : ∀ x ∈ e.source, h (e x) = h p + ∑ i, σ i * x i ^ 2)
    {R : Real} (hR : 0 < R) (hRs : closedBall (0 : E2) R ⊆ e.source)
    {K : Set S2} (hKl : K ⊆ h ⁻¹' {h p})
    (hKout : Disjoint K (e '' closedBall (0 : E2) R)) :
    ∃ H : S2 → Real, ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H ∧
      IsCompact (H ⁻¹' {h p}) ∧
      (∀ q, H q = h p → mfderiv (𝓡 2) 𝓘(Real, Real) H q ≠ 0) ∧
      (∀ q ∈ K, H =ᶠ[𝓝 q] h) ∧ K ⊆ H ⁻¹' {h p} := by
  obtain ⟨H, hH, _, _, _, hout, hregular⟩ :=
    exists_regularization_of_morse_level hh hunique e he0 hep he hei σ hσ hform hR hRs
  have hgerm (q : S2) (hq : q ∈ K) : H =ᶠ[𝓝 q] h :=
    hout q (fun hq' => disjoint_left.mp hKout hq hq')
  refine ⟨H, hH, (isClosed_singleton.preimage hH.continuous).isCompact,
    hregular, hgerm, ?_⟩
  intro q hq
  exact (hgerm q hq).eq_of_nhds.trans (hKl hq)

end Poincare.Manifold.Schoenflies.SaddleLevel
