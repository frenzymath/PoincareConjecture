import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Extension.Canonical











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem exists_late_reference_canonical_control
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hR : H.r₀⁻¹ ^ 2 < (H.terminalConnection P04).scalarCurvature x) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t (ht : t ∈ Ico H.reference.tMinus T), s < t →
        t ∉ H.singularTimes ∧ H.r₀⁻¹ ^ 2 < H.reference.scalar t x ∧
          GeneralizedCanonicalControl (F := F) t (H.reference.forward t ht x)
            H.epsilon H.constant := by
  obtain ⟨a, haT, hscalar⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    ((H.tendsto_terminal_scalarCurvature P04 x).eventually_const_lt hR)
  obtain ⟨b, hbref, hbT, hregular⟩ := H.exists_regular_collar
  refine ⟨max a b, hbref.trans_le (le_max_right _ _), max_lt haT hbT, ?_⟩
  intro t ht hst
  have hregular_t := hregular t ⟨((le_max_right a b).trans_lt hst).le, ht.2⟩
  have hscalar_t := hscalar ⟨(le_max_left a b).trans_lt hst, ht.2⟩
  refine ⟨hregular_t, hscalar_t, H.canonical_control t (H.reference.window_subset ht)
    (Or.inr hregular_t) (H.reference.forward t ht x) ?_⟩
  change H.r₀⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature (H.reference.forward t ht x)
  rw [H.reference.scalar_pullback t ht x]
  exact hscalar_t.le



theorem exists_late_extended_canonical_control
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hΩ : H.reference.regularLimitSet.Nonempty) (x : H.regularRegion P04)
    (hR : H.r₀⁻¹ ^ 2 < (H.terminalConnection P04).scalarCurvature x) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t (ht : t ∈ Ico H.reference.tMinus T), s < t →
        t ∉ H.singularTimes ∧ H.r₀⁻¹ ^ 2 < H.reference.scalar t x ∧
          GeneralizedCanonicalControl (F := (H.nonemptyExtension P04 hΩ).extended) t
            ((H.nonemptyExtension P04 hΩ).forward t (H.reference.window_subset ht)
              (H.reference.forward t ht x)) H.epsilon H.constant := by
  obtain ⟨s, hsref, hsT, hcontrol⟩ := H.exists_late_reference_canonical_control P04 x hR
  refine ⟨s, hsref, hsT, ?_⟩
  intro t ht hst
  obtain ⟨hregular, hscalar, hcanonical⟩ := hcontrol t ht hst
  exact ⟨hregular, hscalar, (H.nonemptyExtension P04 hΩ).canonical_control t
    (H.reference.window_subset ht) (H.reference.forward t ht x) H.epsilon H.constant hcanonical⟩



theorem eventually_extended_canonical_control
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hΩ : H.reference.regularLimitSet.Nonempty) (x : H.regularRegion P04)
    (hR : H.r₀⁻¹ ^ 2 < (H.terminalConnection P04).scalarCurvature x) :
    ∀ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      GeneralizedCanonicalControl (F := (H.nonemptyExtension P04 hΩ).extended) t
        ((H.nonemptyExtension P04 hΩ).forward t (H.reference.window_subset ht)
          (H.reference.forward t ht x)) H.epsilon H.constant := by
  obtain ⟨s, hsref, hsT, hcontrol⟩ := H.exists_late_extended_canonical_control P04 hΩ x hR
  filter_upwards [Ioo_mem_nhdsLT hsT] with t ht
  have hreference : t ∈ Ico H.reference.tMinus T := ⟨(hsref.trans ht.1).le, ht.2⟩
  exact ⟨hreference, (hcontrol t hreference ht.1).2.2⟩

end PoincareConjecture.SingularTimeAssumptions
