import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance secondVariationCommutationEndGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCommutationEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationCommutationConnectionGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCommutationConnectionSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

theorem coordinateCovariantU_congr (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q : ℝ × ℝ → E) {W Z : ℝ × ℝ → E} {p : ℝ × ℝ}
    (h : W =ᶠ[𝓝 p] Z) :
    coordinateCovariantU Γ q W p = coordinateCovariantU Γ q Z p := by
  simp only [coordinateCovariantU, coordinatePartialU, h.fderiv_eq, h.eq_of_nhds]

theorem coordinateCovariantU_contDiffOn {Ω : Set (ℝ × ℝ)} {U : Set (ℝ × E)}
    (hΩ : IsOpen Ω) (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q W : ℝ × ℝ → E) (hΓ : ContDiffOn ℝ ∞ Γ U)
    (hq : ContDiffOn ℝ ∞ q Ω) (hW : ContDiffOn ℝ ∞ W Ω)
    (hmap : MapsTo (fun p ↦ (p.1, q p)) Ω U) :
    ContDiffOn ℝ ∞ (coordinateCovariantU Γ q W) Ω :=
  (coordinatePartialU_contDiffOn hΩ W hW).add
    (((hΓ.comp (contDiffOn_fst.prodMk hq) hmap).clm_apply
      (coordinatePartialU_contDiffOn hΩ q hq)).clm_apply hW)

theorem coordinateCovariantS_contDiffOn {Ω : Set (ℝ × ℝ)} {U : Set (ℝ × E)}
    (hΩ : IsOpen Ω) (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q W : ℝ × ℝ → E) (hΓ : ContDiffOn ℝ ∞ Γ U)
    (hq : ContDiffOn ℝ ∞ q Ω) (hW : ContDiffOn ℝ ∞ W Ω)
    (hmap : MapsTo (fun p ↦ (p.1, q p)) Ω U) :
    ContDiffOn ℝ ∞ (coordinateCovariantS Γ q W) Ω :=
  (coordinatePartialS_contDiffOn hΩ W hW).add
    (((hΓ.comp (contDiffOn_fst.prodMk hq) hmap).clm_apply
      (coordinatePartialS_contDiffOn hΩ q hq)).clm_apply hW)

set_option maxHeartbeats 1000000 in
theorem coordinateCovariant_velocity_second {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q : ℝ × ℝ → E) (hq : ContDiffOn ℝ ∞ q Ω)
    (hsym : ∀ p ∈ Ω, ∀ v w : E, Γ (p.1, q p) v w = Γ (p.1, q p) w v)
    {p : ℝ × ℝ} (hp : p ∈ Ω) (hΓ : DifferentiableAt ℝ Γ (p.1, q p)) :
    coordinateCovariantU Γ q (coordinateCovariantU Γ q (coordinatePartialS q)) p =
      coordinateCovariantS Γ q (coordinateCovariantU Γ q (coordinatePartialU q)) p +
      (fderiv ℝ Γ (p.1, q p) (0, coordinatePartialU q p)
          (coordinatePartialS q p) (coordinatePartialU q p) -
        fderiv ℝ Γ (p.1, q p) (0, coordinatePartialS q p)
          (coordinatePartialU q p) (coordinatePartialU q p) +
        Γ (p.1, q p) (coordinatePartialU q p)
          (Γ (p.1, q p) (coordinatePartialS q p) (coordinatePartialU q p)) -
        Γ (p.1, q p) (coordinatePartialS q p)
          (Γ (p.1, q p) (coordinatePartialU q p) (coordinatePartialU q p))) -
      fderiv ℝ Γ (p.1, q p) (1, 0) (coordinatePartialU q p) (coordinatePartialU q p) := by
  have hqp := (hq p hp).contDiffAt (hΩ.mem_nhds hp)
  have hY := ((coordinatePartialU_contDiffOn hΩ q hq) p hp).contDiffAt (hΩ.mem_nhds hp)
  have htor : coordinateCovariantU Γ q (coordinatePartialS q) =ᶠ[𝓝 p]
      coordinateCovariantS Γ q (coordinatePartialU q) := by
    filter_upwards [hΩ.mem_nhds hp] with r hr
    exact coordinateCovariant_torsion Γ q ((hq r hr).contDiffAt (hΩ.mem_nhds hr))
      (hsym r hr)
  rw [coordinateCovariantU_congr Γ q htor]
  have h := coordinateCovariant_commutator Γ q (coordinatePartialU q) hqp hY hΓ
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
