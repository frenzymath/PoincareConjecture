import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapMixed
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Euclidean BoundaryTangential

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin (n + 1))

local instance : NormedAddCommGroup (Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup
    (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ
    (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem finite_continuous_bound {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} [Finite ι] {K : Set Plane} (hK : IsCompact K)
    {f : ι → Plane → E} (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C : ℝ, ∀ i z, z ∈ K → ‖f i z‖ ≤ C := by
  let := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuousOn_pi.mpr hf)
  exact ⟨C, fun i z hz => (norm_le_pi_norm (fun j => f j z) i).trans (hC z hz)⟩

private theorem fderiv_eqOn_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set Plane} (hO : IsOpen O) {u U : Plane → E} (heq : EqOn U u O) :
    EqOn (fderiv ℝ U) (fderiv ℝ u) O := by
  intro z hz
  have h : U =ᶠ[𝓝 z] u := mem_of_superset (hO.mem_nhds hz) heq
  exact h.fderiv_eq

theorem compact_mixed_quadratic_system_contDiffOn_closure
    {K W0 W1 W2 W3 O : Set Plane} {T : Set Target}
    (hK : IsCompact K) (hKD : UniqueDiffOn ℝ K)
    (hW0 : IsOpen W0) (hW0c : IsCompact (closure W0))
    (hWK : W0 ∩ {z : Plane | 0 ≤ z 0} ⊆ K)
    (hW1 : IsOpen W1) (hW1c : IsCompact (closure W1)) (h10 : closure W1 ⊆ W0)
    (hW2 : IsOpen W2) (hW2c : IsCompact (closure W2)) (h21 : closure W2 ⊆ W1)
    (hW3 : IsOpen W3) (hW3c : IsCompact (closure W3)) (h32 : closure W3 ⊆ W2)
    (hO : IsOpen O) (hOc : IsCompact (closure O)) (hconv : Convex ℝ O)
    (hOH : O ⊆ Half) (hO3 : closure O ⊆ W3) (hT : IsOpen T)
    {u : Plane → Target}
    {B : Fin (n + 1) → Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    (hc : ContDiffOn ℝ 1 u K) (hs : ContDiffOn ℝ ∞ u (W0 ∩ Half))
    (hu : ∀ j, MemWkp 2 2 (fun z => u z j) (W0 ∩ Half))
    (hB : ∀ j, ContDiffOn ℝ 2 (B j) T) (huT : MapsTo u K T)
    (hn : ∀ z ∈ K, z 0 = 0 →
      (fderivWithin ℝ u K z (EuclideanSpace.single 0 1)) 0 = 0)
    (ht : ∀ j : Fin (n + 1), j ≠ 0 → ∀ z ∈ K, z 0 = 0 → u z j = 0)
    (heq : ∀ j z, z ∈ W0 ∩ Half →
      -(∑ i : Fin 2, (fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) j) =
      quadraticForcing (B j) u (fun i => boundaryVectorPartial i u) z) :
    ContDiffOn ℝ 2 u (closure O) := by
  have hS0 : IsOpen (W0 ∩ Half) := hW0.inter isOpen_halfSpace
  have hSK : W0 ∩ Half ⊆ K := by
    intro z hz
    exact hWK ⟨hz.1, (show 0 < z 0 from hz.2).le⟩
  obtain ⟨U, hUc, hU⟩ := m64_exists_continuous_extension hK.isClosed hc.continuousOn
  have hUS : EqOn U u (W0 ∩ Half) := hU.mono hSK
  have hUD : EqOn (fderiv ℝ U) (fderiv ℝ u) (W0 ∩ Half) := fderiv_eqOn_open hS0 hUS
  have hUDD : EqOn (fderiv ℝ (fderiv ℝ U)) (fderiv ℝ (fderiv ℝ u)) (W0 ∩ Half) :=
    fderiv_eqOn_open hS0 hUD
  have hUs : ContDiffOn ℝ ∞ U (W0 ∩ Half) := hs.congr hUS
  have hUh (j : Fin (n + 1)) : MemWkp 2 2 (fun z => U z j) (W0 ∩ Half) := by
    apply (MemWkp_congr_ae (by norm_num) hS0 ?_).mpr (hu j)
    filter_upwards [ae_restrict_mem hS0.measurableSet] with z hz
    exact congrArg (fun y => y j) (hUS hz)
  have hwithin (z : Plane) (hz : z ∈ W0 ∩ Half) :
      fderiv ℝ U z = fderivWithin ℝ u K z := by
    rw [hUD hz, fderivWithin_of_mem_nhds (mem_of_superset (hS0.mem_nhds hz) hSK)]
  have hDC : ContinuousOn (fderivWithin ℝ u K) K := hc.continuousOn_fderivWithin hKD le_rfl
  let d : Plane → ℝ := fun z => (fderivWithin ℝ u K z (EuclideanSpace.single 0 1)) 0
  have hdc : ContinuousOn d K :=
    (EuclideanSpace.proj 0).continuous.comp_continuousOn (hDC.clm_apply continuousOn_const)
  let dK : C(K, ℝ) := ⟨fun z => d z, continuousOn_iff_continuous_domRestrict.mp hdc⟩
  obtain ⟨v, hv⟩ := dK.exists_restrict_eq hK.isClosed
  have hvK : EqOn v d K := fun z hz => ContinuousMap.congr_fun hv ⟨z, hz⟩
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hDC
  obtain ⟨C0, hC0⟩ := finite_continuous_bound hK
    (fun j => (hB j).continuousOn.comp hc.continuousOn huT)
  have hDB (j : Fin (n + 1)) : ContDiffOn ℝ 1 (fderiv ℝ (B j)) T :=
    (hB j).fderiv_of_isOpen hT (by norm_num)
  obtain ⟨C1, hC1⟩ := finite_continuous_bound hK
    (fun j => (hDB j).continuousOn.comp hc.continuousOn huT)
  obtain ⟨C2, hC2⟩ := finite_continuous_bound hK
    (fun j => ((hDB j).continuousOn_fderiv_of_isOpen hT le_rfl).comp hc.continuousOn huT)
  have hreg : ContDiffOn ℝ 2 U (closure O) := by
    apply mixed_quadratic_system_contDiffOn_closure hW0 hW0c hW1 hW1c h10
      hW2 hW2c h21 hW3 hW3c h32 hO hOc hconv hOH hO3 hT hUc hUs hUh hB
    · intro z hz
      rw [hUS hz]
      exact huT (hSK hz)
    · intro j z hz
      rw [hUS hz]
      exact hC0 j z (hSK hz)
    · intro j z hz
      rw [hUS hz]
      exact hC1 j z (hSK hz)
    · intro j z hz
      rw [hUS hz]
      exact hC2 j z (hSK hz)
    · intro i z hz
      change ‖fderiv ℝ U z (EuclideanSpace.single i 1)‖ ≤ A
      rw [hwithin z hz]
      calc
        _ ≤ ‖fderivWithin ℝ u K z‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          (fderivWithin ℝ u K z).le_opNorm _
        _ = ‖fderivWithin ℝ u K z‖ := by simp
        _ ≤ A := hA z (hSK hz)
    · exact v.continuous
    · intro z hz hz0
      have hzK := hWK ⟨hz, by simp [hz0]⟩
      exact (hvK hzK).trans (hn z hzK hz0)
    · intro z hz
      rw [hvK (hSK hz)]
      change (fderivWithin ℝ u K z (EuclideanSpace.single 0 1)) 0 =
        (fderiv ℝ U z (EuclideanSpace.single 0 1)) 0
      rw [hwithin z hz]
    · intro j hj z hz hz0
      have hzK := hWK ⟨hz, by simp [hz0]⟩
      rw [hU hzK]
      exact ht j hj z hzK hz0
    · intro j z hz
      simpa only [hUDD hz, quadraticForcing, boundaryVectorPartial, hUD hz, hUS hz]
        using heq j z hz
  apply hreg.congr
  have hOK : O ⊆ K := by
    intro z hz
    apply hSK
    refine ⟨?_, hOH hz⟩
    have hz3 := hO3 (subset_closure hz)
    have hz2 := h32 (subset_closure hz3)
    have hz1 := h21 (subset_closure hz2)
    exact h10 (subset_closure hz1)
  intro z hz
  exact (hU (closure_minimal hOK hK.isClosed hz)).symm

end PoincareConjecture.M64.RampTransport
