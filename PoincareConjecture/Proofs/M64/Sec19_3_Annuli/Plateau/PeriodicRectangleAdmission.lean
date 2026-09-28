import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import Mathlib.Algebra.Order.ToIntervalMod

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64Annulus_exists_eqOn_rectangle_of_lipschitz
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (hc0 : Function.Periodic c0 curvePeriod)
    (hc1 : Function.Periodic c1 curvePeriod)
    (f : LoopPlane → M)
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      f (annulusPoint curvePeriod s) = f (annulusPoint 0 s))
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod, f (annulusPoint x 1) = c1 x)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :
    ∃ B : M64Annulus g c0 c1, EqOn B.map f m64AnnulusDomain := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let F : LoopPlane → M := fun p =>
    f (annulusPoint (toIcoMod hP 0 (p 0)) (p 1))
  have hF : EqOn F f m64AnnulusDomain := by
    intro p hp
    have hpcoord : annulusPoint (p 0) (p 1) = p := by
      ext i
      fin_cases i <;> rfl
    by_cases hx : p 0 < curvePeriod
    · have hm : toIcoMod hP 0 (p 0) = p 0 :=
        (toIcoMod_eq_self hP).mpr (by simpa using And.intro hp.1 hx)
      simp only [F, hm, hpcoord]
    · have hx' : p 0 = curvePeriod := le_antisymm hp.2.1 (le_of_not_gt hx)
      have hm : toIcoMod hP 0 curvePeriod = 0 := by
        calc
          _ = toIcoMod hP 0 0 := by
            simpa only [zero_add] using toIcoMod_add_right hP 0 0
          _ = 0 := (toIcoMod_eq_self hP).mpr (by simp [hP])
      change f (annulusPoint (toIcoMod hP 0 (p 0)) (p 1)) = f p
      rw [hx', hm, ← hpcoord, hx']
      exact (hseam (p 1) ⟨hp.2.2.1, hp.2.2.2⟩).symm
  have hperiodic (x s : ℝ) :
      F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s) := by
    change f (annulusPoint (toIcoMod hP 0 (x + curvePeriod)) s) =
      f (annulusPoint (toIcoMod hP 0 x) s)
    rw [toIcoMod_add_right]
  have hmod (c : ℝ → M) (hc : Function.Periodic c curvePeriod) (x : ℝ) :
      c (toIcoMod hP 0 x) = c x := by
    have h := hc.zsmul (toIcoDiv hP 0 x) (toIcoMod hP 0 x)
    rw [toIcoMod_add_toIcoDiv_zsmul] at h
    exact h.symm
  have hlowerF (x : ℝ) : F (annulusPoint x 0) = c0 x := by
    change f (annulusPoint (toIcoMod hP 0 x) 0) = c0 x
    rw [hlower _ (Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)), hmod c0 hc0]
  have hupperF (x : ℝ) : F (annulusPoint x 1) = c1 x := by
    change f (annulusPoint (toIcoMod hP 0 x) 1) = c1 x
    rw [hupper _ (Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)), hmod c1 hc1]
  have hLipF : ∀ x y : m64AnnulusDomain,
      g.edist (F x) (F y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    rw [hF x.property, hF y.property]
    exact hLip x y
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← MeasureTheory.measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨B, hB, _⟩ := m64Annulus_of_lipschitz g F
    (hcontinuous.congr hF) hperiodic hlowerF hupperF hL hLipF hfinite
    (lt_add_one (∫ p in m64AnnulusDomain, m60AreaDensity g F p))
  exact ⟨B, hB ▸ hF⟩

end PoincareConjecture
