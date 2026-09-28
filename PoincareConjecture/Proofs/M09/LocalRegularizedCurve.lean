import PoincareConjecture.Proofs.M09.CompactRegularizedEquation
import PoincareConjecture.Proofs.M09.GeometricUniqueness
import Mathlib.Topology.Order.DenselyOrdered








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

structure IsLocalRegularizedCurveOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (U : Set ℝ) : Prop where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U
  equation : ∀ s ∈ U, LocalRegularizedEquation F T γ s

theorem IsLocalRegularizedCurveOn.mono {J : Set ℝ} {F : RicciFlow n M J}
    {T : ℝ} {γ : ℝ → M} {U V : Set ℝ} (h : IsLocalRegularizedCurveOn F T γ U)
    (hVU : V ⊆ U) : IsLocalRegularizedCurveOn F T γ V :=
  ⟨h.smooth.mono hVU, fun s hs ↦ h.equation s (hVU hs)⟩

theorem IsLocalRegularizedCurveOn.congr {J : Set ℝ} {F : RicciFlow n M J}
    {T : ℝ} {γ δ : ℝ → M} {U : Set ℝ} (h : IsLocalRegularizedCurveOn F T γ U)
    (hU : IsOpen U) (heq : Set.EqOn γ δ U) : IsLocalRegularizedCurveOn F T δ U := by
  refine ⟨h.smooth.congr heq.symm, ?_⟩
  intro s hs
  apply (h.equation s hs).congr
  filter_upwards [hU.mem_nhds hs] with t ht using heq ht

theorem IsLocalRegularizedCurveOn.of_locally {J : Set ℝ} {F : RicciFlow n M J}
    {T : ℝ} {γ : ℝ → M} {U : Set ℝ}
    (h : ∀ s ∈ U, ∃ (δ : ℝ → M) (V : Set ℝ), IsOpen V ∧ s ∈ V ∧
      IsLocalRegularizedCurveOn F T δ V ∧ γ =ᶠ[𝓝 s] δ) :
    IsLocalRegularizedCurveOn F T γ U := by
  have hp : ∀ s ∈ U, ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ s ∧
      LocalRegularizedEquation F T γ s := by
    intro s hs
    obtain ⟨δ, V, hV, hsV, hδ, heq⟩ := h s hs
    exact ⟨(hδ.smooth.contMDiffAt (hV.mem_nhds hsV)).congr_of_eventuallyEq heq,
      (hδ.equation s hsV).congr heq.symm⟩
  exact ⟨fun s hs ↦ (hp s hs).1.contMDiffWithinAt, fun s hs ↦ (hp s hs).2⟩

theorem localRegularizedCurve_eventuallyEq {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (γ δ : ℝ → M)
    (U : Set ℝ) (hU : IsOpen U) (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : IsLocalRegularizedCurveOn F T γ U) (hδ : IsLocalRegularizedCurveOn F T δ U)
    (s0 : ℝ) (hs0 : s0 ∈ U)
    (hphase : curvePhase (n := n) γ s0 = curvePhase (n := n) δ s0) :
    γ =ᶠ[𝓝 s0] δ := by
  obtain ⟨a, c, _, hKnhds, hKU⟩ := exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds hs0)
  have hsI : s0 ∈ Set.Ioo a c := Icc_mem_nhds_iff.mp hKnhds
  have hK : UniqueDiffOn ℝ (Set.Icc a c) := uniqueDiffOn_Icc (hsI.1.trans hsI.2)
  have hIU : Set.Ioo a c ⊆ U := Set.Ioo_subset_Icc_self.trans hKU
  obtain ⟨Eγ, heγ⟩ := exists_regularizedExtensionOn_compact F hM04 T b hb hwindow γ
    U (Set.Icc a c) hU hKU isCompact_Icc hK (hKU.trans htime) hγ.smooth
    (fun s hs ↦ hγ.equation s (hKU hs))
  obtain ⟨Eδ, heδ⟩ := exists_regularizedExtensionOn_compact F hM04 T b hb hwindow δ
    U (Set.Icc a c) hU hKU isCompact_Icc hK (hKU.trans htime) hδ.smooth
    (fun s hs ↦ hδ.equation s (hKU hs))
  have hγd : ∀ s ∈ Set.Icc a c, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s :=
    fun s hs ↦ (hγ.smooth.contMDiffAt (hU.mem_nhds (hKU hs))).mdifferentiableAt (by simp)
  have hδd : ∀ s ∈ Set.Icc a c, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) δ s :=
    fun s hs ↦ (hδ.smooth.contMDiffAt (hU.mem_nhds (hKU hs))).mdifferentiableAt (by simp)
  let EγI := restrictVelocityExtension γ (Set.Icc a c) (Set.Ioo a c)
    Set.Ioo_subset_Icc_self hK isOpen_Ioo.uniqueDiffOn hγd Eγ
  let EδI := restrictVelocityExtension δ (Set.Icc a c) (Set.Ioo a c)
    Set.Ioo_subset_Icc_self hK isOpen_Ioo.uniqueDiffOn hδd Eδ
  exact regularizedCurve_eventuallyEq F hM04 T b hb hwindow γ δ (Set.Ioo a c) isOpen_Ioo
    (hIU.trans htime) (hγ.smooth.mono hIU) (hδ.smooth.mono hIU) EγI EδI
    (fun s hs ↦ regularizedEquation_restrict F T γ (Set.Icc a c) (Set.Ioo a c)
      Set.Ioo_subset_Icc_self hK isOpen_Ioo.uniqueDiffOn hγd Eγ s hs
      (heγ s (Set.Ioo_subset_Icc_self hs)))
    (fun s hs ↦ regularizedEquation_restrict F T δ (Set.Icc a c) (Set.Ioo a c)
      Set.Ioo_subset_Icc_self hK isOpen_Ioo.uniqueDiffOn hδd Eδ s hs
      (heδ s (Set.Ioo_subset_Icc_self hs))) s0 hsI hphase

theorem localRegularizedCurve_phase_eqOn {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (γ δ : ℝ → M)
    (U : Set ℝ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : IsLocalRegularizedCurveOn F T γ U) (hδ : IsLocalRegularizedCurveOn F T δ U)
    (s0 : ℝ) (hs0 : s0 ∈ U)
    (hphase : curvePhase (n := n) γ s0 = curvePhase (n := n) δ s0) :
    Set.EqOn (curvePhase (n := n) γ) (curvePhase (n := n) δ) U := by
  let : T2Space (TangentBundle (𝓡 n) M) := tangentBundle_t2Space
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  let A : Set U := {s | curvePhase (n := n) γ s = curvePhase (n := n) δ s}
  have hclosed : IsClosed A := isClosed_eq
    (curvePhase_contMDiffOn γ U hU hγ.smooth).continuousOn.domRestrict
    (curvePhase_contMDiffOn δ U hU hδ.smooth).continuousOn.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal := localRegularizedCurve_eventuallyEq F hM04 T b hb hwindow γ δ U hU
      htime hγ hδ t t.property ht
    exact continuousAt_subtype_val.preimage_mem_nhds (curvePhase_eventuallyEq hlocal)
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨s0, hs0⟩, hphase⟩
  intro t ht
  have hm : (⟨t, ht⟩ : U) ∈ A := by rw [hAll]; trivial
  exact hm

end PoincareConjecture.Proofs.M09
