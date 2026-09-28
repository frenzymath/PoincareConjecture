import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteCurrentTraces
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCirclePeriodicity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64FiniteAnnulusCurrent_seam
    (A : M64Annulus g c0 c1) {v : ℝ → LoopPlane → M}
    (hbase : ∀ p, v 0 p = A.map p)
    (hperiodic : ∀ t x y, v t (annulusPoint (x + curvePeriod) y) =
      v t (annulusPoint x y))
    (hc : ∀ i : Fin 2, ContinuousOn (m64FiniteAnnulusCurrent g v i) m64AnnulusDomain)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map
      {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1}) (i : Fin 2) :
    ∀ y ∈ Icc (0 : ℝ) 1,
      m64FiniteAnnulusCurrent g v i (annulusPoint curvePeriod y) =
        m64FiniteAnnulusCurrent g v i (annulusPoint 0 y) := by
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hstrip : IsOpen {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} :=
    isOpen_Ioo.preimage (by fun_prop)
  have hline (x : ℝ) : Continuous (fun y : ℝ => annulusPoint x y) := by
    unfold annulusPoint
    fun_prop
  have hclosed (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      ContinuousOn (fun y => m64FiniteAnnulusCurrent g v i (annulusPoint x y))
        (Icc (0 : ℝ) 1) :=
    (hc i).comp (hline x).continuousOn (fun _ hy => ⟨hx.1, hx.2, hy.1, hy.2⟩)
  have heq : EqOn
      (fun y => m64FiniteAnnulusCurrent g v i (annulusPoint curvePeriod y))
      (fun y => m64FiniteAnnulusCurrent g v i (annulusPoint 0 y)) (Ioo (0 : ℝ) 1) := by
    intro y hy
    have hcol (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
        mfderivWithin (𝓡 2) (𝓡 n) (v 0) m64AnnulusDomain (annulusPoint x y)
          (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        mfderiv (𝓡 2) (𝓡 n) A.map (annulusPoint x y)
          (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      rw [show v 0 = A.map from funext hbase]
      rw [mfderivWithin_eq_mfderiv
        (m64AnnulusDomain_uniqueDiffOn.uniqueMDiffOn _ ⟨hx.1, hx.2, hy.1.le, hy.2.le⟩)
        ((hA.contMDiffAt (hstrip.mem_nhds (show annulusPoint x y ∈
          {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} from hy))).mdifferentiableAt (by simp))]
    have hshift : annulusPoint curvePeriod 0 + annulusPoint 0 y =
        annulusPoint curvePeriod y := by
      ext j
      fin_cases j <;> simp [annulusPoint]
    have hd := m64Annulus_mfderiv_periodic A (annulusPoint 0 y)
    rw [hshift] at hd
    have htime : (fun t => v t (annulusPoint curvePeriod y)) =
        fun t => v t (annulusPoint 0 y) := by
      funext t
      simpa only [zero_add] using hperiodic t 0 y
    have hvelocity := congrArg (fun f : ℝ → M =>
      (curveVelocity (n := n) f 0 : EuclideanSpace ℝ (Fin n))) htime
    have hdata : (v 0 (annulusPoint curvePeriod y),
        (curveVelocity (fun t => v t (annulusPoint curvePeriod y)) 0 :
          EuclideanSpace ℝ (Fin n)),
        (mfderivWithin (𝓡 2) (𝓡 n) (v 0) m64AnnulusDomain (annulusPoint curvePeriod y)
          (EuclideanSpace.basisFun (Fin 2) ℝ i) : EuclideanSpace ℝ (Fin n))) =
      (v 0 (annulusPoint 0 y),
        (curveVelocity (fun t => v t (annulusPoint 0 y)) 0 : EuclideanSpace ℝ (Fin n)),
        (mfderivWithin (𝓡 2) (𝓡 n) (v 0) m64AnnulusDomain (annulusPoint 0 y)
          (EuclideanSpace.basisFun (Fin 2) ℝ i) : EuclideanSpace ℝ (Fin n))) := by
      refine Prod.ext (congrFun htime 0) (Prod.ext hvelocity ?_)
      rw [hcol curvePeriod ⟨hperiod, le_rfl⟩, hcol 0 ⟨le_rfl, hperiod⟩, hd]
      rfl
    exact congrArg (fun q : M × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      g.inner q.1 q.2.1 q.2.2) hdata
  exact heq.of_subset_closure (hclosed curvePeriod ⟨hperiod, le_rfl⟩)
    (hclosed 0 ⟨le_rfl, hperiod⟩) Ioo_subset_Icc_self
    (by rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)])

end PoincareConjecture
