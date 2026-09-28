import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Scalar
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope














set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.CylinderGluing




theorem exists_centered_scalar_extension
    (h : RoundCylinderSpace → ℝ)
    (hh : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h)
    (hzero : ∀ q : UnitTwoSphere, h (q, 0) = 0)
    (hpos : ∀ q : UnitTwoSphere, 0 < deriv (fun t : ℝ => h (q, t)) 0) :
    ∃ (r : ℝ) (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ (∀ p : RoundCylinderSpace, (D p).1 = p.1) ∧
      (∀ q : UnitTwoSphere, D (q, 0) = (q, 0)) ∧
      (∀ q : UnitTwoSphere, StrictMono (fun t : ℝ => (D (q, t)).2)) ∧
      (∀ p : RoundCylinderSpace, (D p).2 ≤ 0 ↔ p.2 ≤ 0) ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r → D (q, t) = (q, h (q, t)) := by
  obtain ⟨r, D, hr, hfst, hagree⟩ := exists_scalar_collar_extension h hh hpos
  have hfix (q : UnitTwoSphere) : D (q, 0) = (q, 0) := by
    rw [hagree q 0 (by simpa using hr), hzero q]
  have hmono (q : UnitTwoSphere) : StrictMono (fun t : ℝ => (D (q, t)).2) := by
    have hc : Continuous (fun t : ℝ => (D (q, t)).2) :=
      continuous_snd.comp (D.continuous.comp (continuous_const.prodMk continuous_id))
    have hi : Function.Injective (fun t : ℝ => (D (q, t)).2) := by
      intro s t hst
      have hd : D (q, s) = D (q, t) :=
        Prod.ext ((hfst (q, s)).trans (hfst (q, t)).symm) hst
      exact congrArg Prod.snd (D.injective hd)
    rcases hc.strictMono_of_inj hi with hm | hm
    · exact hm
    · have heq : (fun t : ℝ => (D (q, t)).2) =ᶠ[𝓝 0] fun t => h (q, t) := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
          (by simpa using hr : |(0 : ℝ)| < r)] with t ht
        exact congrArg Prod.snd (hagree q t ht)
      have hd : deriv (fun t : ℝ => (D (q, t)).2) 0 =
          deriv (fun t : ℝ => h (q, t)) 0 := heq.deriv_eq
      exact False.elim (not_lt_of_ge (hd ▸ hm.antitone.deriv_nonpos) (hpos q))
  refine ⟨r, D, hr, hfst, hfix, hmono, ?_, hagree⟩
  intro p
  have h := (hmono p.1).le_iff_le (a := p.2) (b := 0)
  rw [hfix] at h
  exact h

end PoincareConjecture.CylinderGluing
