import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.LocalLevel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension
import Mathlib.Topology.OpenPartialHomeomorph.Composition












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)



def openLevelSetHomeomorphLocalLevel {n : ℕ} (f : E n → ℝ) (U : Opens (E n)) (c : ℝ) :
    openLevelSet f U c ≃ₜ {x : E n // x ∈ U ∧ f x = c} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _



theorem exists_unitSlice_chart_of_regular_potential
    {X : Type*} [MetricSpace X] {p : X} (hcomparison : RayComparison p)
    {n : ℕ} (F : OpenPartialHomeomorph (E (n + 1)) (AsymptoticCone p hcomparison))
    (f : E (n + 1) → ℝ) (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x ∈ F.source, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hpotential : ∀ x ∈ F.source,
      (asymptoticConeRadius hcomparison (F x) : ℝ) ^ 2 / 2 = f x)
    {x : E (n + 1)} (hx : x ∈ F.source) (hfx : f x = 1 / 2) :
    ∃ C : OpenPartialHomeomorph (E n) (AsymptoticConeUnitSlice p hcomparison),
      (⟨F x, (cone_unit_iff_radial_potential_eq hcomparison F f hpotential hx).mpr hfx⟩ :
        AsymptoticConeUnitSlice p hcomparison) ∈ C.target ∧
      C.target ⊆ {z : AsymptoticConeUnitSlice p hcomparison | z.1 ∈ F.target} := by
  let U : Opens (E (n + 1)) := ⟨F.source, F.open_source⟩
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n (1 / 2)
  let z : openLevelSet f U (1 / 2) := ⟨⟨x, hx⟩, hfx⟩
  let T : Opens (AsymptoticConeUnitSlice p hcomparison) :=
    ⟨{w | w.1 ∈ F.target}, isOpen_unitLink_chart_target hcomparison F⟩
  let H : openLevelSet f U (1 / 2) ≃ₜ T :=
    (openLevelSetHomeomorphLocalLevel f U (1 / 2)).trans
      (unitLinkLocalLevelHomeomorph hcomparison F f hpotential)
  have hT : Nonempty T := ⟨H z⟩
  let J := T.openPartialHomeomorphSubtypeCoe hT
  let B := H.toOpenPartialHomeomorph.trans J
  let C := (chartAt (E n) z).symm.trans B
  have hzchart : chartAt (E n) z z ∈ C.source := by
    refine ⟨mem_chart_target (E n) z, ?_⟩
    change (chartAt (E n) z).symm (chartAt (E n) z z) ∈ B.source
    rw [(chartAt (E n) z).left_inv (mem_chart_source (E n) z)]
    change z ∈ Set.univ ∩ H ⁻¹' J.source
    simp [J]
  have hCz : C (chartAt (E n) z z) =
      (⟨F x, (cone_unit_iff_radial_potential_eq hcomparison F f hpotential hx).mpr hfx⟩ :
        AsymptoticConeUnitSlice p hcomparison) := by
    change (H ((chartAt (E n) z).symm (chartAt (E n) z z))).1 = _
    rw [(chartAt (E n) z).left_inv (mem_chart_source (E n) z)]
    rfl
  refine ⟨C, hCz ▸ C.map_source hzchart, ?_⟩
  intro w hw
  simpa only [J, Opens.openPartialHomeomorphSubtypeCoe_target, T, Opens.coe_mk] using hw.1.1

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.LeviCivitaData

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)




theorem exists_unitSlice_chart_of_local_radial_potential
    {X : Type*} [MetricSpace X] {p : X}
    (hcomparison : Poincare.AncientVolume.ScalarRatio.RayComparison p)
    {n : ℕ} {g : RiemannianMetric (n + 1) (E (n + 1))} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (E (n + 1))
      (Poincare.AncientVolume.ScalarRatio.AsymptoticCone p hcomparison))
    (f : E (n + 1) → ℝ)
    (hf : ContMDiffOn (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f F.source)
    (hQ : ∀ x ∈ F.source, D.levelQ f x = 2 * f x)
    (hpotential : ∀ x ∈ F.source,
      (Poincare.AncientVolume.ScalarRatio.asymptoticConeRadius hcomparison (F x) : ℝ) ^ 2 / 2 = f x)
    {x : E (n + 1)} (hx : x ∈ F.source) (hfx : f x = 1 / 2) :
    ∃ C : OpenPartialHomeomorph (E n)
      (Poincare.AncientVolume.ScalarRatio.AsymptoticConeUnitSlice p hcomparison),
      (⟨F x, (Poincare.AncientVolume.ScalarRatio.cone_unit_iff_radial_potential_eq
        hcomparison F f hpotential hx).mpr hfx⟩ :
        Poincare.AncientVolume.ScalarRatio.AsymptoticConeUnitSlice p hcomparison) ∈ C.target ∧
      C.target ⊆ {z : Poincare.AncientVolume.ScalarRatio.AsymptoticConeUnitSlice p hcomparison |
        z.1 ∈ F.target} := by
  obtain ⟨ψ, hψ, hψeq⟩ := Poincare.Manifold.exists_contMDiff_eq_near F.open_source hf hx
  have hψx : ψ x = 1 / 2 := hψeq.self_of_nhds.trans hfx
  have hpos : ∀ᶠ y in 𝓝 x, 0 < ψ y := by
    exact (hψ x).continuousAt.eventually (eventually_gt_nhds (by rw [hψx]; norm_num))
  have hsourceNear : ∀ᶠ y in 𝓝 x, y ∈ F.source := F.open_source.mem_nhds hx
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp
    (hψeq.and (hsourceNear.and hpos))
  have hVF : V ⊆ F.source := fun y hy => (hVsub hy).2.1
  have hreg : ∀ y ∈ V, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ψ y ≠ 0 := by
    intro y hy hd
    have heq : ψ =ᶠ[𝓝 y] f := by
      filter_upwards [hVo.mem_nhds hy] with z hz
      exact (hVsub hz).1
    have hgrad : D.gradient ψ y = D.gradient f y := by
      simp only [gradient, Poincare.mvfderiv_eq_of_eventuallyEq heq]
    have hz : D.gradient ψ y = 0 := (g.gradient_eq_zero_iff_mfderiv_eq_zero ψ y).mpr hd
    have hzero : D.levelQ f y = 0 := by
      simp only [levelQ, ← hgrad, hz, map_zero]
    rw [hQ y (hVF hy), ← (hVsub hy).1] at hzero
    linarith [(hVsub hy).2.2]
  let F' := F.restr V
  have hF'source : F'.source = V := by
    rw [OpenPartialHomeomorph.restr_source, hVo.interior_eq, inter_eq_right.mpr hVF]
  have hx' : x ∈ F'.source := hF'source.symm ▸ hxV
  have hpotential' : ∀ y ∈ F'.source,
      (Poincare.AncientVolume.ScalarRatio.asymptoticConeRadius hcomparison (F' y) : ℝ) ^ 2 / 2 =
        ψ y := by
    intro y hy
    have hyV : y ∈ V := hF'source ▸ hy
    exact (hpotential y (hVF hyV)).trans (hVsub hyV).1.symm
  obtain ⟨C, hC, hCT⟩ :=
    Poincare.AncientVolume.ScalarRatio.exists_unitSlice_chart_of_regular_potential
      hcomparison F' ψ hψ (fun y hy => hreg y (hF'source ▸ hy)) hpotential' hx' hψx
  refine ⟨C, hC, ?_⟩
  intro z hz
  exact (hCT hz).1

end PoincareConjecture.LeviCivitaData
