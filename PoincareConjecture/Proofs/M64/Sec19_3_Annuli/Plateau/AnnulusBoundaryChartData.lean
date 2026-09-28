import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusBoundaryError
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakVariation













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

omit [IsManifold (𝓡 n) ∞ M] in


theorem exists_lower_chart_columns
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : Continuous e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    {F : LoopPlane → M} (hF : ContinuousOn F O)
    (hFae : F =ᵐ[volume.restrict O] A.lowerExtensionMap)
    {a : LoopPlane} (ha : a ∈ O) :
    ∃ (b : M) (L : E →L[ℝ] EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 < R ∧ closedBall a R ⊆ O ∧
      (∀ p ∈ closedBall a R,
        F p ∈ (extChartAt (𝓡 n) b).source ∧ L (e (F p)) = extChartAt (𝓡 n) b (F p)) ∧
      ContinuousOn (fun p => L (e (F p))) (closedBall a R) ∧
      MemLp (fun p => L (e (F p))) 2 (volume.restrict (ball a R)) ∧
      (∀ i, MemLp (fun p => L (A.lowerExtensionColumn i p)) 2 (volume.restrict (ball a R))) ∧
      ∀ i j, HasWeakPartialDeriv i (fun p => L (A.lowerExtensionColumn i p) j)
        (fun p => L (e (F p)) j) (ball a R) := by
  obtain ⟨b, hb, L, hL⟩ := hread (F a)
  have hFa : ContinuousAt F a := hF.continuousAt (m64AnnulusLowerDomain_isOpen.mem_nhds ha)
  have hnear : {p | F p ∈ (extChartAt (𝓡 n) b).source ∧
      L (e (F p)) = extChartAt (𝓡 n) b (F p)} ∈ 𝓝 a :=
    inter_mem (hFa.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb))
      (hL.comp_tendsto hFa)
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (m64AnnulusLowerDomain_isOpen.mem_nhds ha) hnear)
  have hRO : closedBall a R ⊆ O := fun p hp => (hball hp).1
  have hBO : ball a R ⊆ O := ball_subset_closedBall.trans hRO
  have hobs : (e ∘ A.lowerExtensionMap) =ᵐ[volume.restrict O] (e ∘ F) := by
    filter_upwards [hFae] with p hp
    exact congrArg e hp.symm
  have hFM := (A.lower_extension_memLp hc0).1.ae_eq hobs
  refine ⟨b, L, R, hR, hRO, (fun p hp => (hball hp).2),
    (L.continuous.comp_continuousOn (he.comp_continuousOn hF)).mono hRO,
    (L.comp_memLp' hFM).mono_measure (Measure.restrict_mono hBO le_rfl),
    (fun i => (L.comp_memLp' ((A.lower_extension_memLp hc0).2 i)).mono_measure
      (Measure.restrict_mono hBO le_rfl)), ?_⟩
  intro i j
  have hw := m64WeakPartial_comp_linear (A.lower_extension_memLp hc0).1
    ((A.lower_extension_memLp hc0).2 i) (A.lower_extension_weak_partial hc0 i) L j
  have hwF : HasWeakPartialDeriv i (fun p => L (A.lowerExtensionColumn i p) j)
      (fun p => L (e (F p)) j) O := by
    apply m64WeakPartialDeriv_ae_congr ?_ EventuallyEq.rfl hw
    filter_upwards [hobs] with p hp
    exact congrArg (fun v : E => L v j) hp
  exact hwF.restrict isOpen_ball hBO




theorem weighted_exists_lower_critical_coordinates [CompactSpace M] [T2Space M]
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus) :
    ∃ F : LoopPlane → M, ContinuousOn F O ∧
      F =ᵐ[volume.restrict O] A.lowerExtensionMap ∧
      (∀ x ∈ Ioo (0 : ℝ) curvePeriod, F (annulusPoint x 0) = c0 x) ∧
      ∀ x ∈ Ioo (0 : ℝ) curvePeriod,
        ∃ (b : M) (L : E →L[ℝ] EuclideanSpace ℝ (Fin n)) (R : ℝ)
          (u : LoopPlane → EuclideanSpace ℝ (Fin n)),
          0 < R ∧ closedBall (annulusPoint x 0) R ⊆ O ∧ Continuous u ∧
          EqOn u (fun p => L (e (F p))) (closedBall (annulusPoint x 0) R) ∧
          MapsTo u (closedBall (annulusPoint x 0) R) (extChartAt (𝓡 n) b).target ∧
          EqOn ((extChartAt (𝓡 n) b).symm ∘ u) F (closedBall (annulusPoint x 0) R) ∧
          (∀ i, MemLp (fun p => L (A.lowerExtensionColumn i p)) 2
            (volume.restrict (ball (annulusPoint x 0) R))) ∧
          (∀ i j, HasWeakPartialDeriv i (fun p => L (A.lowerExtensionColumn i p) j)
            (fun p => u p j) (ball (annulusPoint x 0) R)) ∧
          ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ phi →
            tsupport phi ⊆ ball (annulusPoint x 0) ((R / 4) * Real.exp (-1)) →
            (∀ p : LoopPlane, p 1 ≤ 0 → phi p = 0) →
            let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
            let W := fun (i : Fin 2) (p : LoopPlane) => L (A.lowerExtensionColumn i p)
            let rate := fun p =>
              (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
                  2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
                modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
                  2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2
            IntegrableOn rate (ball (annulusPoint x 0) (R / 2)) ∧
              (∫ p in ball (annulusPoint x 0) (R / 2), rate p) = 0 := by
  obtain ⟨F, hF, hFae, htrace⟩ := A.weighted_lower_continuous_representative
    g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmodulus hmin
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hfixed (p : LoopPlane) (hp : p ∈ O) (hp1 : p 1 < 0) : F p = c0 (p 0) :=
    A.lower_representative_eq_boundary_below hc0.continuous hF hFae htrace p hp hp1.le
  refine ⟨F, hF, hFae, htrace, ?_⟩
  intro x hx
  have ha : annulusPoint x 0 ∈ O :=
    ⟨hx.1, hx.2, by norm_num [annulusPoint], by norm_num [annulusPoint]⟩
  obtain ⟨b, L, R, hR, hRO, hchart, hu0, -, hW, hw⟩ :=
    A.exists_lower_chart_columns he.continuous hread hce hF hFae ha
  obtain ⟨u, hu, heq⟩ := m64_exists_continuous_extension isClosed_closedBall hu0
  have hcoord (p : LoopPlane) (hp : p ∈ closedBall (annulusPoint x 0) R) :
      u p = extChartAt (𝓡 n) b (F p) := (heq hp).trans (hchart p hp).2
  have huT : MapsTo u (closedBall (annulusPoint x 0) R) (extChartAt (𝓡 n) b).target := by
    intro p hp
    rw [hcoord p hp]
    exact (extChartAt (𝓡 n) b).map_source (hchart p hp).1
  have hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) F (closedBall (annulusPoint x 0) R) := by
    intro p hp
    change (extChartAt (𝓡 n) b).symm (u p) = F p
    rw [hcoord p hp, (extChartAt (𝓡 n) b).left_inv (hchart p hp).1]
  have hwu (i : Fin 2) (j : Fin n) : HasWeakPartialDeriv i
      (fun p => L (A.lowerExtensionColumn i p) j) (fun p => u p j)
      (ball (annulusPoint x 0) R) := by
    apply m64WeakPartialDeriv_ae_congr ?_ EventuallyEq.rfl (hw i j)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hp
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j)
      (heq (ball_subset_closedBall hp)).symm
  refine ⟨b, L, R, u, hR, hRO, hu, heq, huT, hmap, hW, hwu, ?_⟩
  intro phi hp hps hpzero
  exact A.weighted_lower_coordinate_variation_eq_zero g he hei.isEmbedding hce Q hQ
    (fun q => hB _ (mem_range_self q)) hdiag modulus hmin F hFae hfixed b
    hR hRO hu huT hW hwu hmap phi hp hps hpzero

end PoincareConjecture.M64ObservedWeakAnnulus
