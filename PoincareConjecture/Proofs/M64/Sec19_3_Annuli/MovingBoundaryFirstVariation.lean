import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DouglasMorreyInterface
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MinimalAnnulusFamily

















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

private theorem annulusForward_of_quotient_tendsto
    {f : ℝ → ℝ} {d rate t : ℝ}
    (hquot : Tendsto (fun h : ℝ => (f (t + h) - f t) / h)
      (𝓝[>] 0) (𝓝 d)) (hd : d ≤ rate) :
    AnnulusForwardDerivativeBound f rate t := by
  intro eta heta
  have hstrict : d < rate + eta :=
    lt_of_le_of_lt hd (lt_add_of_pos_right rate heta)
  have hev := hquot.eventually (Iio_mem_nhds hstrict)
  filter_upwards [hev] with h hh
  exact le_of_lt hh








structure M64MovingBoundaryFirstVariationCertificate
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (c0 c1 : ℝ → ℝ → P.charts.Point) (rate : ℝ → ℝ) where
  data : ∀ t ∈ Set.Icc a b,
    M64MinimalAnnulusData
      (g := P.flow.metric t)
      (c0 := fun x => c0 x t) (c1 := fun x => c1 x t)
  branch : ∀ (t : ℝ) (ht : t ∈ Set.Icc a b),
    M64AnnulusBranchAwareFirstVariationCertificate
      (M := P.charts.Point)
      ((data t ht).annulus)
  swept : ∀ (t : ℝ) (ht : t ∈ Set.Ico a b), ∃ d : ℝ,
    d ≤ rate t ∧
    ∃ B : ∀ h : ℝ,
      M64Annulus (P.flow.metric (t + h))
        (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
      (B 0).area = (data t ⟨ht.1, le_of_lt ht.2⟩).annulus.area ∧
      Tendsto
        (fun h : ℝ =>
          ((B h).area -
            (data t ⟨ht.1, le_of_lt ht.2⟩).annulus.area) / h)
        (𝓝[>] 0) (𝓝 d)

namespace M64MovingBoundaryFirstVariationCertificate





noncomputable def to_minimal_annulus_family
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point} {rate : ℝ → ℝ}
    (C : M64MovingBoundaryFirstVariationCertificate P c0 c1 rate) :
    M64MinimalAnnulusFamily P c0 c1 rate := by
  refine ⟨C.data, ?_⟩
  intro t ht eta heta
  have htcc : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt ht.2⟩
  obtain ⟨d, hd, B, hbase, hquot⟩ := C.swept t ht
  have hstrict : d < rate t + eta :=
    lt_of_le_of_lt hd (lt_add_of_pos_right (rate t) heta)
  have hev := hquot.eventually (Iio_mem_nhds hstrict)
  filter_upwards [hev, self_mem_nhdsWithin] with h hh hpos
  refine ⟨B h, ?_⟩
  have hmul := (div_le_iff₀ hpos).mp (le_of_lt hh)
  have hmin : (C.data t htcc).annulus.area =
      m64FlowAnnulusArea P c0 c1 t := by
    simpa only [m64FlowAnnulusArea] using
      (C.data t htcc).area_minimal
  rw [hmin] at hmul
  linarith

end M64MovingBoundaryFirstVariationCertificate

end PoincareConjecture
