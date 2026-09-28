import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseLift

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

theorem closed_strip_exists_circle_phase {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (f : LoopPlane → C.Point)
    (hf : ContinuousOn f {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hfi : ContMDiffOn (𝓡 2) (𝓡 1) ∞ f
      {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1})
    (hper : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = C.quotient 0)
    {delta : ℝ} (hupper : ∀ x, f (annulusPoint x 1) = C.quotient delta) :
    ∃ (L : LoopPlane → ℝ) (c : ℝ), Continuous L ∧
      ContDiffOn ℝ ∞ L {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} ∧
      (∀ p, p 1 ∈ Icc (0 : ℝ) 1 → C.quotient (L p) = f p) ∧
      (∀ x, L (annulusPoint x 0) = 0) ∧
      (∀ x, L (annulusPoint x 1) = c) ∧
      (∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s)) ∧
      C.quotient c = C.quotient delta := by
  let := C.chartedSpace
  let R : LoopPlane → LoopPlane := fun p => annulusPoint (p 0) (max 0 (min 1 (p 1)))
  have hR : Continuous R := by unfold R annulusPoint; fun_prop
  have hRm (p : LoopPlane) : (R p) 1 ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hRe (p : LoopPlane) (hp : p 1 ∈ Icc (0 : ℝ) 1) : R p = p := by
    ext i
    fin_cases i
    · rfl
    · change max 0 (min 1 (p 1)) = p 1
      rw [min_eq_right hp.2, max_eq_right hp.1]
  have hbase : C.quotient 0 = (f ∘ R) (annulusPoint 0 0) := by
    rw [Function.comp_apply, hRe _ (by change (0 : ℝ) ∈ Icc 0 1; norm_num)]
    exact (hlower 0).symm
  let cov := AddCircle.isCoveringMap_coe circumference
  obtain ⟨L, hL, -⟩ := cov.existsUnique_continuousMap_lifts
    ⟨f ∘ R, hf.comp_continuous hR hRm⟩ (annulusPoint 0 0) 0 hbase
  have hquot (p : LoopPlane) : C.quotient (L p) = f (R p) := congrFun hL.2 p
  have hq (p : LoopPlane) (hp : p 1 ∈ Icc (0 : ℝ) 1) :
      C.quotient (L p) = f p := by rw [hquot, hRe p hp]
  have hline (s : ℝ) : Continuous (fun x => annulusPoint x s) := by
    unfold annulusPoint
    fun_prop
  have h0 (x : ℝ) : L (annulusPoint x 0) = 0 := by
    have heq := cov.eq_of_comp_eq (L.continuous.comp (hline 0)) continuous_const
      (show (fun y => (L (annulusPoint y 0) : AddCircle circumference)) =
        (fun _ : ℝ => ((0 : ℝ) : AddCircle circumference)) from by
          funext y
          exact (hq _ (by change (0 : ℝ) ∈ Icc 0 1; norm_num)).trans (hlower y))
      0 hL.1
    exact congrFun heq x
  let c := L (annulusPoint 0 1)
  have hc : C.quotient c = C.quotient delta :=
    (hq _ (by change (1 : ℝ) ∈ Icc 0 1; norm_num)).trans (hupper 0)
  have h1 (x : ℝ) : L (annulusPoint x 1) = c := by
    have heq := cov.eq_of_comp_eq (L.continuous.comp (hline 1)) continuous_const
      (show (fun y => (L (annulusPoint y 1) : AddCircle circumference)) =
        (fun _ : ℝ => (c : AddCircle circumference)) from by
          funext y
          exact ((hq _ (by change (1 : ℝ) ∈ Icc 0 1; norm_num)).trans
            (hupper y)).trans hc.symm) 0 rfl
    exact congrFun heq x
  have hLi : ContDiffOn ℝ ∞ L {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} := by
    intro p hp
    have hopen : IsOpen {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} :=
      isOpen_Ioo.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous
    have heq : C.quotient ∘ L =ᶠ[𝓝 p] f := by
      filter_upwards [hopen.mem_nhds hp] with q hq'
      exact hq q ⟨hq'.1.le, hq'.2.le⟩
    have hcomp := (hfi.contMDiffAt (hopen.mem_nhds hp)).congr_of_eventuallyEq heq
    exact (contMDiffAt_iff_contDiffAt.mp
      ((C.quotient_local_diffeomorph (L p)).contMDiffAt_of_comp
        (I := 𝓡 2) le_rfl L.continuous.continuousAt hcomp)).contDiffWithinAt
  refine ⟨L, c, L.continuous, hLi, hq, h0, h1, ?_, hc⟩
  have hshift : Continuous (fun p : LoopPlane =>
      annulusPoint (p 0 + curvePeriod) (p 1)) := by unfold annulusPoint; fun_prop
  have heq := cov.eq_of_comp_eq (L.continuous.comp hshift) L.continuous
    (show (fun p : LoopPlane => (L (annulusPoint (p 0 + curvePeriod) (p 1)) :
      AddCircle circumference)) = (fun p => (L p : AddCircle circumference)) from by
        funext p
        change C.quotient (L _) = C.quotient (L p)
        rw [hquot, hquot]
        exact hper (p 0) (max 0 (min 1 (p 1))))
    (annulusPoint 0 0) (by change L (annulusPoint (0 + curvePeriod) 0) = L _; rw [h0, h0])
  intro x s
  exact congrFun heq (annulusPoint x s)

end PoincareConjecture.M64
