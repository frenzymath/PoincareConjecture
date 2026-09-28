import PoincareConjecture.Proofs.M76.Mathlib.PrescribedCapCollarIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.PositiveDiskCapHeight
import PoincareConjecture.Proofs.M76.Mathlib.PositiveCapLevelImages









set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_positive_cap_collar_isotopy
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : Disjoint d Q.space) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ f : E × ℝ → E, (∀ p, (C p : E) = f p) ∧
      ∃ (r : E → ℝ) (p : E), FinitePiecewiseAffineOn r d ∧ p ∈ d \ b ∧
        (∀ x ∈ d, r x ∈ Icc (2 / 3) 1 ∧ (r x = 1 ↔ x ∈ b)) ∧
        r p = 2 / 3 ∧ (∀ x ∈ d, r x = 2 / 3 ↔ x = p) ∧
        ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
          EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
          ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
            (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
              FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
            Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
            Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
            (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
            ∀ t : Icc (-ε) ε,
              FinitePiecewiseAffineOn (H t : E → E) d ∧
              FinitePiecewiseAffineOn (H t : E → E) T ∧
              (∀ x ∈ d, A (H t x) = (t : ℝ) * r x) ∧
              IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
              (0 < (t : ℝ) →
                (∀ c : ℝ, c < (t : ℝ) * (2 / 3) ∨ (t : ℝ) < c →
                  (H t '' d) ∩ {x | A x = c} = ∅) ∧
                (H t '' d) ∩ {x | A x = (t : ℝ) * (2 / 3)} = {H t p} ∧
                (H t '' d) ∩ {x | A x = (t : ℝ)} = H t '' b ∧
                ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
                  IsFinitePLBallPair (ℝ × ℝ) ((H t '' d) ∩ {x | A x ≤ (t : ℝ) * a})
                    ((H t '' d) ∩ {x | A x = (t : ℝ) * a})) ∧
              (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
              ∀ c : ℝ,
                ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g (f (x, 0)))
                    (upper x + (t : ℝ) * g (f (x, upper x)))} ≃ₜ
                    ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
                  ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g (f (x, 0)))
                      (upper x + (t : ℝ) * g (f (x, upper x)))},
                    ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                      (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                      ((t : ℝ) * g (f (x, 0)) = c ↔ (p : E × ℝ).2 = 0) ∧
                      (upper x + (t : ℝ) * g (f (x, upper x)) = c ↔
                        (p : E × ℝ).2 = upper x) := by
  obtain ⟨r, hr, hrbounds, ⟨p, hp, hpmin, hpunique⟩, hlevels⟩ :=
    hd.exists_positive_cap_height
  obtain ⟨f, hfval, g, hgT, hgn, hgr, hgQ, hgU, ε, hε, H, hglobal,
      hc, hci, hformula, hall⟩ :=
    hC.exists_prescribed_cap_collar_isotopy hupper A hheight hd hdplane hr
      (fun x hx => (by norm_num : (0 : ℝ) ≤ 2 / 3).trans (hrbounds x hx).1.1)
      v hv Q hQ (fun x hx => ((disjoint_left.mp hQd) hx.1 hx.2).elim) hU hdU
  refine ⟨f, hfval, r, p, hr, hp, hrbounds, hpmin, hpunique, g, hgT, hgn,
    hgr, hgQ, hgU, ε, hε, H, hglobal, hc, hci, hformula, fun t => ?_⟩
  obtain ⟨hHd, hHT, hheight, hball, hcharts⟩ := hall t
  refine ⟨hHd, hHT, hheight, hball, ?_, ?_, hcharts⟩
  · intro ht
    exact hHd.positive_cap_level_classification (H t).injective.injOn ht hheight
      hrbounds hp.1 hpmin hpunique hlevels hd.1
  · intro c
    have hinter : (H t '' d) ∩ (H t '' T) = H t '' b := by
      rw [← image_inter (H t).injective, hcap]
    ext x
    have hx := Set.ext_iff.mp hinter x
    simp only [mem_inter_iff] at *
    tauto

end Homeomorph
