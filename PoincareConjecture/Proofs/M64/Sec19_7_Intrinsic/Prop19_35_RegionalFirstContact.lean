import PoincareConjecture.Proofs.M64.Mathlib.MeasurableCappedFirstExitOpen
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AnnularRegionEntry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalContactComparison
import Mathlib.MeasureTheory.MeasurableSpace.Constructions












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology Matrix

namespace PoincareConjecture






theorem m64Intrinsic_exists_measurable_regional_contact_times
    {a b : ℝ} (hinj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    {C U V : Set AnnulusCoordinates} (hC : IsCompact C)
    (havoid : ∀ p ∈ Ioo a b, intrinsicAnnulusBoundary 1 p ∉ C)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ C)
    (hfV : frontier V = frontier U) (hsub : closure U ⊆ standardAnnulusDomain)
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : Continuous e)
    (normal : ℝ → AnnulusCoordinates)
    (hbase : ∀ p ∈ Ioo a b, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p ∈ Ioo a b, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hinward : ∀ p ∈ Ioo a b, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    {R : ℝ} (hR : 0 < R) (annularHeight : ℝ → ℝ)
    (hAnn : ∀ p ∈ Ioo a b, 0 < annularHeight p ∧
      (annularHeight p = R ∨ ‖e !₂[p, annularHeight p]‖ = 1 ∨
        ‖e !₂[p, annularHeight p]‖ = 2)) :
    ∃ height : ℝ → ℝ, Measurable height ∧
      (∀ p ∉ Ioo a b, height p = 0) ∧
      ∀ p ∈ Ioo a b, 0 < height p ∧ height p ≤ R ∧ height p ≤ annularHeight p ∧
        (∀ t ∈ Ioo (0 : ℝ) (height p), e !₂[p, t] ∈ U) ∧
        e !₂[p, height p] ∈ closure U ∧
        (height p = R ∨ e !₂[p, height p] ∈ frontier U) := by
  classical
  let P := Ioo a b
  let u : P × ℝ → AnnulusCoordinates := fun z => e !₂[z.1.val, z.2]
  have hu : Continuous u := he.comp (by fun_prop)
  have henter (p : P) : ∃ eta : ℝ, 0 < eta ∧
      ∀ t ∈ Ioo (0 : ℝ) eta, u (p, t) ∈ U := by
    exact m64Intrinsic_inward_curve_enters_annular_region hinj p.property hC
      (havoid p p.property) hU hV hdisj hfU hfV hsub
      (hbase p p.property) (hderiv p p.property) (hinward p p.property)
  obtain ⟨h, hh, hcontact⟩ :=
    m64_exists_measurable_capped_first_exit_open hu hU hR henter
  let height : ℝ → ℝ := fun p => if hp : p ∈ Ioo a b then h ⟨p, hp⟩ else 0
  have hmeasurable : Measurable height :=
    hh.dite (g := fun _ => (0 : ℝ)) measurable_const measurableSet_Ioo
  have heq (p : ℝ) (hp : p ∈ Ioo a b) : height p = h ⟨p, hp⟩ := dif_pos hp
  refine ⟨height, hmeasurable, ?_, ?_⟩
  · intro p hp
    exact dif_neg hp
  · intro p hp
    rw [heq p hp]
    have hs := hcontact ⟨p, hp⟩
    have hle := m64Intrinsic_regional_contact_le_annulus_contact hU hsub hs.2.1
      (hAnn p hp).1 hs.2.2.1 (hAnn p hp).2
    exact ⟨hs.1, hs.2.1, hle, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

end PoincareConjecture
