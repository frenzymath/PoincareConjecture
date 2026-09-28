import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAnnulusClampedLift

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

private def radialStripClamp (p : LoopPlane) : LoopPlane :=
  annulusPoint (p 0) (projIcc 0 1 (by norm_num) (p 1))

private theorem radialStripClamp_eq {p : LoopPlane} (hp : p 1 ∈ Icc (0 : ℝ) 1) :
    radialStripClamp p = p := by
  ext i
  fin_cases i <;> simp [radialStripClamp, annulusPoint,
    projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hp]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem annulus_full_strip_exists_circle_phase
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map {p | p 1 ∈ Ioo (0 : ℝ) 1})
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x, P.circle.quotient (L0 x) = (c0 x).2)
    {d : ℝ} (hshift : ∀ x, L0 (x + curvePeriod) = L0 x + d) :
    ∃ L : LoopPlane → ℝ, Continuous L ∧
      ContDiffOn ℝ 1 L {p | p 1 ∈ Ioo (0 : ℝ) 1} ∧
      (∀ p, p 1 ∈ Icc (0 : ℝ) 1 → P.circle.quotient (L p) = (A.map p).2) ∧
      (∀ x, L (annulusPoint x 0) = L0 x) ∧
      ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hP : curvePeriod ≠ 0 := ne_of_gt (by unfold curvePeriod; positivity)
  let T := fun p : LoopPlane => (p 0 / curvePeriod, p 1)
  have hT : Continuous T := by dsimp only [T]; fun_prop
  have hclamp (p : LoopPlane) :
      M64Uniformization.scalarAnnulusClamp (T p) = radialStripClamp p := by
    simp only [M64Uniformization.scalarAnnulusClamp, T, radialStripClamp, mul_div_cancel₀ _ hP]
  have hAc : Continuous (A.map ∘ radialStripClamp) := by
    have hc := (M64Uniformization.scalarAnnulus_clamped_lift A).1.comp hT
    simpa only [Function.comp_def, hclamp] using hc
  let f := fun p => (A.map (radialStripClamp p)).2
  have hf : Continuous f := continuous_snd.comp hAc
  have hclampLower (x : ℝ) : radialStripClamp (annulusPoint x 0) = annulusPoint x 0 :=
    radialStripClamp_eq ⟨le_rfl, zero_le_one⟩
  have hbase (x : ℝ) : P.circle.quotient (L0 x) = f (annulusPoint x 0) := by
    dsimp only [f]
    rw [hclampLower, A.lower_boundary]
    exact hzero x
  let cov := AddCircle.isCoveringMap_coe circumference
  obtain ⟨L, hL, -⟩ := cov.existsUnique_continuousMap_lifts
    ⟨f, hf⟩ (annulusPoint 0 0) (L0 0) (hbase 0)
  have hquot (p : LoopPlane) : P.circle.quotient (L p) = f p := congrFun hL.2 p
  have hquotS (p : LoopPlane) (hp : p 1 ∈ Icc (0 : ℝ) 1) :
      P.circle.quotient (L p) = (A.map p).2 := by
    rw [hquot]
    dsimp only [f]
    rw [radialStripClamp_eq hp]
  have hstrip : IsOpen {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} :=
    isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) 1
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).of_le (by simp)
  have hregular : ContDiffOn ℝ 1 L {p | p 1 ∈ Ioo (0 : ℝ) 1} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply contMDiffAt_iff_contDiffAt.mp
    apply (P.circle.quotient_local_diffeomorph (L p)).contMDiffAt_of_comp
      (I := 𝓡 2) (m := 1) (by decide) L.continuous.continuousAt
    have hnear : P.circle.quotient ∘ L =ᶠ[𝓝 p] Prod.snd ∘ A.map := by
      filter_upwards [hstrip.mem_nhds hp] with q hq
      exact hquotS q ⟨hq.1.le, hq.2.le⟩
    exact (((hsnd.comp_contMDiffOn hA) p hp).contMDiffAt
      (hstrip.mem_nhds hp)).congr_of_eventuallyEq hnear
  have hlower : ∀ x, L (annulusPoint x 0) = L0 x := by
    have hc : Continuous (fun x => annulusPoint x 0) := by unfold annulusPoint; fun_prop
    have heq := cov.eq_of_comp_eq (L.continuous.comp hc) hL0
      (show (fun x => (L (annulusPoint x 0) : AddCircle circumference)) =
        (fun x => (L0 x : AddCircle circumference)) from by
          funext x
          exact (hquot _).trans (hbase x).symm) 0 hL.1
    exact congrFun heq
  have hper (x s : ℝ) : f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s) := by
    dsimp only [f, radialStripClamp, annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact congrArg Prod.snd (A.periodic x _)
  have hdegree : (d : AddCircle circumference) = 0 := by
    have hh := hper 0 0
    rw [← hbase, ← hbase, hshift] at hh
    change ((L0 0 + d : ℝ) : AddCircle circumference) = (L0 0 : AddCircle circumference) at hh
    rw [AddCircle.coe_add] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  refine ⟨L, L.continuous, hregular, hquotS, hlower, ?_⟩
  have htranslate : Continuous (fun p : LoopPlane =>
      annulusPoint (p 0 + curvePeriod) (p 1)) := by unfold annulusPoint; fun_prop
  have hbaseMap : Continuous (fun p : LoopPlane => annulusPoint (p 0) (p 1)) := by
    unfold annulusPoint
    fun_prop
  have heq := cov.eq_of_comp_eq (L.continuous.comp htranslate)
    ((L.continuous.comp hbaseMap).add continuous_const)
    (show (fun p : LoopPlane => (L (annulusPoint (p 0 + curvePeriod) (p 1)) :
        AddCircle circumference)) =
      (fun p : LoopPlane => ((L (annulusPoint (p 0) (p 1)) + d : ℝ) :
        AddCircle circumference)) from by
          funext p
          rw [AddCircle.coe_add, hdegree, add_zero]
          exact (hquot _).trans ((hper _ _).trans (hquot _).symm))
    (annulusPoint 0 0) (by
      change L (annulusPoint (0 + curvePeriod) 0) = L (annulusPoint 0 0) + d
      rw [hlower, hlower]
      exact hshift 0)
  intro x s
  simpa [Function.comp_def, annulusPoint] using congrFun heq (annulusPoint x s)

end PoincareConjecture.M64
