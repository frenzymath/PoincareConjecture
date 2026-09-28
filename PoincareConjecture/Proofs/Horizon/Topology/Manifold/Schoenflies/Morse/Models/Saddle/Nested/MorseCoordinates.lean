import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalPoint
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.MorseCoordinates.Chart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.MorseCoordinates.Rescaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_saddle_coordinates_above_nested_cut :
    ∃ p : S2, 1 < height p ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ∧
      ∃ e : OpenPartialHomeomorph E2 S2,
        0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        ∀ x ∈ e.source, height (e x) = height p - (x 0)^2 + (x 1)^2 := by
  obtain ⟨p, hl, hu, hx, hy, hp, hheight⟩ := exists_critical_point_above_nested_cut
  let z := (p : E3) 2
  have hz : 0 < 1-z^2 := by dsimp [z]; nlinarith
  have hn : ((p : E3) 0)^2 + z^2 = 1 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy] at hn
    nlinarith
  have hroot : (p : E3) 0 = -meridianRoot z := by
    have hs := Real.sq_sqrt hz.le
    have hnonneg := Real.sqrt_nonneg (1-z^2)
    dsimp [meridianRoot]
    nlinarith
  have hcrit : meridianRoot z * (2*z-1) = (3/10)*z := by
    have h := (critical_point_coordinates hp).2
    rw [hroot] at h
    change -meridianRoot z * (2*z-1) + (3/10)*z = 0 at h
    nlinarith
  obtain ⟨Q, hQ0, hQzero, hQdom, hQ, hQi, hform⟩ :=
    exists_chartHeight_signed_square_coordinates hl hu hcrit
  let C := negativeSphereChart z
  have hC0 : 0 ∈ C.source := negativeSphereChart_zero_mem hz
  have hCp : C 0 = p := by
    apply Subtype.ext
    rw [negativeSphereChart_zero hz]
    ext i
    fin_cases i <;> simp [hroot, hy, z]
  have hQC (x : E2) (hx : x ∈ Q.source) : Q x ∈ C.source := by
    rw [negativeSphereChart_source]
    exact hQdom hx
  let e := Q.trans C
  have hes (x : E2) (hx : x ∈ e.source) : x ∈ Q.source := hx.1
  have heq (x : E2) : e x = C (Q x) := rfl
  refine ⟨p, hheight, hp, e, ⟨hQ0, by simpa [hQzero] using hC0⟩,
    by simpa [heq, hQzero] using hCp, ?_, ?_, ?_⟩
  · exact (negativeSphereChart_smooth z).comp
      (hQ.contMDiffOn.mono inter_subset_left) (fun x hx => hQC x hx.1)
  · exact hQi.contMDiffOn.comp
      (negativeSphereChart_symm_smooth z).contMDiffOn (fun _ hx => hx.2)
  · intro x hx
    rw [heq, height_negativeSphereChart (hQC x hx.1), hform x hx.1]
    rw [← height_negativeSphereChart hC0, hCp]

end Poincare.Manifold.Schoenflies.Saddle.Nested
