import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClosedC1BoundaryLabels









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m64ClosedStripTrace_label_contDiff
    {e : M → EuclideanSpace ℝ (Fin m)} (he : ContMDiff (𝓡 n) (𝓡 m) ∞ e)
    (hread : M60.SUChartReadable (n := n) e) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c)
    (hregular : ∀ t, curveVelocity (n := n) c t ≠ 0)
    {phi : ℝ → ℝ} (hphi : Continuous phi) {U : LoopPlane → M}
    (hU : ContMDiffOn (𝓡 2) (𝓡 n) 1 U {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (htrace : ∀ x, U (annulusPoint x y) = c (phi x)) : ContDiff ℝ 1 phi := by
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  have hobs : ContDiff ℝ 1 (e ∘ c) := (he1.comp hc).contDiff
  have hUobs : ContDiffOn ℝ 1 (e ∘ U) {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} :=
    (he1.comp_contMDiffOn hU).contDiffOn
  have haxis : ContDiff ℝ 1 (fun x : ℝ => annulusPoint x y) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using! (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => y))
  have hmaps : MapsTo (fun x : ℝ => annulusPoint x y) univ
      {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} := fun _ _ => hy
  have hcomp : ContDiffOn ℝ 1 ((e ∘ c) ∘ phi) univ :=
    (hUobs.comp haxis.contDiffOn hmaps).congr (fun x _ => congrArg e (htrace x).symm)
  have hglobal : ContDiff ℝ 1 ((e ∘ c) ∘ phi) := contDiffOn_univ.mp hcomp
  exact contDiff_iff_contDiffAt.mpr fun x =>
    M63.contDiffAt_of_comp_immersed_curve one_ne_zero hphi.continuousAt hobs.contDiffAt
      (m64ObservedCurve_deriv_ne_zero he hread hc hregular (phi x)) hglobal.contDiffAt

end PoincareConjecture
