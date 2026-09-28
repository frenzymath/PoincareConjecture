import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAngularCuts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Band" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (0 : ℝ) 1)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarNormalizedCoverMap_differentiableAt {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) {z : Cover} (hz : z ∈ scalarCoverStrip) :
    DifferentiableAt ℝ (scalarNormalizedCoverMap H V P) z := by
  have hU := ((scalarCoverPotential_smooth hHs).contDiffAt
    (scalarCoverStrip_isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hVnorm : DifferentiableAt ℝ (fun y => V y / P) z := by
    convert! ((hdV z hz).const_smul P⁻¹).differentiableAt using 1
    ext y
    simp [div_eq_mul_inv, mul_comm]
  exact hU.prodMk hVnorm

theorem scalarNormalizedCoverMap_integer_cover {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ z : Cover ∂volume, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 →
      ∃ n : ℤ, z + (0, (n : ℝ)) ∈ scalarNormalizedCoverMap H V P '' Band := by
  let F := scalarNormalizedCoverMap H V P
  have hnull : volume (F '' scalarAngularCuts) = 0 := scalarAngularCuts_image_measure_zero
    (fun z hz => scalarNormalizedCoverMap_differentiableAt D hHs hdV P hz)
  have hae : ∀ᵐ z : Cover ∂volume, z ∉ F '' scalarAngularCuts := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  have hsurj := scalarNormalizedCover_surjective D hHc hHs hlap hinner houter
    (fun z hz => (hdV z hz).continuousAt.continuousWithinAt) hdV hP hdeck hrange
  filter_upwards [hae] with z hzNot hzQ
  obtain ⟨x, hx⟩ := hsurj (⟨z, hzQ.1⟩ : scalarPotentialStrip)
  have hxval : F (x : Cover) = z := congrArg Subtype.val hx
  have hxNot : (x : Cover) ∉ scalarAngularCuts :=
    fun h => hzNot ⟨x, h, hxval⟩
  let n : ℤ := ⌊(x : Cover).2⌋
  have hxne : (x : Cover).2 ≠ (n : ℝ) := by
    intro heq
    apply hxNot
    exact mem_iUnion.mpr ⟨n, x.property, heq⟩
  have hfract : 0 < Int.fract (x : Cover).2 := Int.fract_pos.mpr hxne
  let y : Cover := (x : Cover) - (0, (n : ℝ))
  have hy : y ∈ Band := by
    refine ⟨?_, ?_⟩
    · simpa only [y, Prod.fst_sub, sub_zero] using
        (show (x : Cover).1 ∈ Ioo (1 : ℝ) 2 from x.property)
    · exact ⟨hfract, Int.fract_lt_one _⟩
  refine ⟨-n, y, hy, ?_⟩
  have hshift := scalarNormalizedCoverMap_sub_int (H := H) hP.ne' hdeck x.property n
  change F y = F (x : Cover) - (0, (n : ℝ)) at hshift
  change F y = z + (0, ((-n : ℤ) : ℝ))
  rw [hshift, hxval]
  ext <;> simp [sub_eq_add_neg]

theorem scalarNormalizedCoverMap_image_area_ge_one {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) :
    1 ≤ volume (scalarNormalizedCoverMap H V P '' Band) := by
  have hEopen : IsOpen (scalarNormalizedCoverMap H V P '' Band) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨z, hz, rfl⟩
    exact scalarNormalizedCoverMap_nhds_le_map D hHc hHs hlap hinner houter hdV hP.ne' hz.1
      (Filter.image_mem_map ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hz))
  exact scalar_area_ge_one_of_integer_cover hEopen.measurableSet
    (scalarNormalizedCoverMap_integer_cover D hHc hHs hlap hinner houter hdV hP hdeck hrange)

end PoincareConjecture.M64Uniformization
