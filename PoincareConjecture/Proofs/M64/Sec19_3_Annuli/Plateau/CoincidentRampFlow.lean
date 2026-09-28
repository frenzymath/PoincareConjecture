import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CoincidentRampC2Reparametrization
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelC2Transport
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessFields
import PoincareConjecture.Statements.M64Annulus













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem coincident_degreeOneRamp_flows_zero_area
    (P : M62.CircleProductData F circumference) (c0 c1 : ℝ → ℝ → P.charts.Point)
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (L0 : M63PositiveDegreeLift P (fun x => c0 x a))
    (L1 : M63PositiveDegreeLift P (fun x => c1 x a))
    (hd0 : L0.degree = 1) (hd1 : L1.degree = 1)
    (himage : range (fun x => c0 x a) = range (fun x => c1 x a)) :
    ∃ phi : ℝ ≃ₜ ℝ,
      (∀ t ∈ Icc a b, ∀ x, c0 (phi x) t = c1 x t) ∧
      ∀ t ∈ Icc a b,
        ∃ A : M64Annulus (P.flow.metric t) (fun x => c0 x t) (fun x => c1 x t),
          A.area = 0 ∧ m64FlowAnnulusArea P c0 c1 t = 0 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  have hab : a ≤ b := by
    obtain ⟨s, hs, -, -, -⟩ := F.nontrivial
    exact hs.1.trans hs.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  obtain ⟨phi, hphi, hpos, hshift, hinit, K, hK⟩ :=
    coincident_degreeOneRamps_reparametrize_C2 P (hc0.periodic a ha) L0 L1 hd0 hd1 himage
  have hcomp := M63.c2ShrinkingCurve_fixedLabel_comp P.flow hc0 hphi hpos hshift
  have heq := M63.c2ShrinkingCurve_unique_closed P.flow isCompact_univ hcomp hc1 hinit
  refine ⟨phi, heq, ?_⟩
  intro t ht
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 (fun x => c0 x t) :=
    (hc0.spatial_regular t ht).of_le (by norm_num)
  obtain ⟨A, -, hA⟩ := m64_zero_area_boundary_collar (P.flow.metric t)
    (fun x => c0 x t) phi hgamma.continuous (hc0.periodic t ht)
    (m64PeriodicC1Curve_metric_lipschitz (P.flow.metric t) hgamma (hc0.periodic t ht))
    phi.continuous hshift ⟨K, K.property, fun x y => by
      simpa only [Real.dist_eq] using hK.dist_le_mul x y⟩
  have htrace : (fun x => c0 x t) ∘ phi = fun x => c1 x t := funext (heq t ht)
  have hinf : m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) ((fun x => c0 x t) ∘ phi) = 0 :=
    le_antisymm ((m64LeastAnnulusArea_le_annulus A).trans_eq hA)
      (m64LeastAnnulusArea_nonneg A)
  change ∃ A : M64Annulus (P.flow.metric t) (fun x => c0 x t) (fun x => c1 x t),
    A.area = 0 ∧ m64LeastAnnulusArea (P.flow.metric t) (fun x => c0 x t) (fun x => c1 x t) = 0
  rw [← htrace]
  exact ⟨A, hA, hinf⟩



theorem m64AnnulusFlowConclusion_of_coincident_degreeOneRamps
    (G : M63AmbientGeometry F) (h : 0 < circumference)
    (c0 c1 : ℝ → ℝ → (G.product circumference h).charts.Point)
    (hc0 : M63C2ShrinkingCurveOn (G.product circumference h).flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn (G.product circumference h).flow c1 (Icc a b))
    (L0 : M63PositiveDegreeLift (G.product circumference h) (fun x => c0 x a))
    (L1 : M63PositiveDegreeLift (G.product circumference h) (fun x => c1 x a))
    (hd0 : L0.degree = 1) (hd1 : L1.degree = 1)
    (himage : range (fun x => c0 x a) = range (fun x => c1 x a)) :
    M64AnnulusFlowConclusion G h c0 c1 := by
  obtain ⟨-, -, hA⟩ := coincident_degreeOneRamp_flows_zero_area
    (G.product circumference h) c0 c1 hc0 hc1 L0 L1 hd0 hd1 himage
  have hzero (t : ℝ) (ht : t ∈ Icc a b) :
      m64FlowAnnulusArea (G.product circumference h) c0 c1 t = 0 :=
    (hA t ht).choose_spec.2
  refine {
    nonempty := fun t ht => ⟨(hA t ht).choose⟩
    bounded_below := fun _ _ => m64AnnulusAreaRange_bddBelow _ _ _
    nonnegative := fun t ht => by rw [hzero t ht]
    continuous := continuousOn_const.congr (fun t ht => hzero t ht)
    forward := ?_
    exponential := ?_ }
  · intro t ht eta heta
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < b - t :=
      nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr ht.2))
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hpos
    change 0 < s at hpos
    have hfuture : t + s ∈ Icc a b := ⟨by linarith [ht.1], by linarith⟩
    rw [hzero (t + s) hfuture, hzero t ⟨ht.1, ht.2.le⟩]
    simpa using heta.le
  · intro s t hs ht _hst
    rw [hzero t ht, hzero s hs, mul_zero]

end PoincareConjecture.M64
