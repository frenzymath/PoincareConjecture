import PoincareConjecture.Proofs.M09.InteriorEndpointFamily
import PoincareConjecture.Proofs.M09.InitialVectorVariation








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

noncomputable def lineInteriorCoordinate (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (c : ℝ) (r : ℝ) : Q :=
  chartAt Q (A.squareFamily Z (Real.sqrt c)) (A.squareFamily (Z + r • W) (Real.sqrt c))

structure LineInteriorFamily (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (c b : ℝ) where
  family : (ℝ × Q) × ℝ → M
  domain : Set ((ℝ × Q) × ℝ)
  parameters : Set (ℝ × Q)
  domain_open : IsOpen domain
  parameters_open : IsOpen parameters
  center_mem : (0, lineInteriorCoordinate A Z W c 0) ∈ parameters
  segment_mem : parameters ×ˢ Set.Icc 0 (Real.sqrt b) ⊆ domain
  smooth : ContMDiffOn (𝓘(ℝ, (ℝ × Q) × ℝ)) (𝓡 n) ∞ family domain
  target_mem : ∀ z ∈ parameters,
    z.2 ∈ (chartAt Q (A.squareFamily Z (Real.sqrt c))).target
  left : ∀ r y, family ((r, y), 0) = p
  right : ∀ r y, family ((r, y), Real.sqrt b) = A.squareFamily (Z + r • W) (Real.sqrt b)
  marked : ∀ r y, family ((r, y), Real.sqrt c) =
    (chartAt Q (A.squareFamily Z (Real.sqrt c))).symm y
  recovery : ∀ z ∈ parameters, ∀ s ∈ Set.Icc 0 (Real.sqrt b),
    family ((z.1, lineInteriorCoordinate A Z W c z.1), s) = A.squareFamily (Z + z.1 • W) s
  coordinate_smooth : ContDiffAt ℝ ∞ (lineInteriorCoordinate A Z W c) 0
  diagonal_mem : ∀ᶠ r in 𝓝 (0 : ℝ), (r, lineInteriorCoordinate A Z W c r) ∈ parameters

set_option backward.isDefEq.respectTransparency false in
theorem exists_lineInteriorFamily (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (c b : ℝ)
    (hc : 0 < c) (hcb : c < b) (hmax : b < τmax) :
    Nonempty (LineInteriorFamily A Z W c b) := by
  let V := (initialVectorVariation A Z W b (hc.trans hcb) hmax).toLVariation
  let H : ℝ × ℝ → M := fun z ↦ A.squareFamily (Z + z.1 • W) z.2
  let U := Prod.swap ⁻¹' V.squareDomain
  have hU : IsOpen U := V.square_open.preimage continuous_swap
  have hV : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z : ℝ × ℝ ↦ V.squareFamily z.1 z.2) V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H U :=
    hV.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn (fun _ hz ↦ hz)
  have hsegment (s : ℝ) (hs : s ∈ Set.Icc 0 (Real.sqrt b)) : (0, s) ∈ U := by
    change (s, (0 : ℝ)) ∈ V.squareDomain
    apply V.square_contains
    exact ⟨by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs,
      neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hH0 : H (0, Real.sqrt c) = A.squareFamily Z (Real.sqrt c) := by
    simp only [H, zero_smul, add_zero]
  obtain ⟨Φ, Ω, N, hΩ, hN, h0N, hNΩ, hΦ, hinfo, hleft, hright, hmarked, hrecovery⟩ :=
    exists_smooth_interior_endpoint_family H U hU hH 0 (Real.sqrt b) (Real.sqrt c)
      ⟨Real.sqrt_pos.mpr hc, Real.sqrt_lt_sqrt hc.le hcb⟩ hsegment
  let e := chartAt Q (A.squareFamily Z (Real.sqrt c))
  let a := lineInteriorCoordinate A Z W c
  have ha : ContDiffAt ℝ ∞ a 0 := by
    have hmem := hsegment (Real.sqrt c)
      ⟨Real.sqrt_nonneg c, Real.sqrt_le_sqrt hcb.le⟩
    have hslice : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞
        (fun r ↦ H (r, Real.sqrt c)) 0 :=
      (hH.contMDiffAt (hU.mem_nhds hmem)).comp 0
        (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt
    have hsource : H (0, Real.sqrt c) ∈ e.source := by
      rw [hH0]
      exact mem_chart_source Q _
    have hchart : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (H (0, Real.sqrt c)) :=
      contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hsource)
    exact (hchart.comp 0 hslice).contDiffAt
  have hcenter : (0, a 0) ∈ N := by
    simpa only [hH0, a, lineInteriorCoordinate, zero_smul, add_zero] using h0N
  have hdiag : ∀ᶠ r in 𝓝 (0 : ℝ), (r, a r) ∈ N :=
    (continuousAt_id.prodMk ha.continuousAt).preimage_mem_nhds (hN.mem_nhds hcenter)
  refine ⟨{
    family := Φ
    domain := Ω
    parameters := N
    domain_open := hΩ
    parameters_open := hN
    center_mem := hcenter
    segment_mem := hNΩ
    smooth := hΦ
    target_mem := ?_
    left := ?_
    right := hright
    marked := ?_
    recovery := ?_
    coordinate_smooth := ha
    diagonal_mem := hdiag
  }⟩
  · intro z hz
    simpa only [hH0] using (hinfo z hz).1
  · intro r y
    exact (hleft r y).trans (A.square_at_zero (Z + r • W))
  · intro r y
    simpa only [hH0] using hmarked r y
  · intro z hz s hs
    simpa only [hH0, H, lineInteriorCoordinate] using hrecovery z hz s hs

end PoincareConjecture.Proofs.M09
