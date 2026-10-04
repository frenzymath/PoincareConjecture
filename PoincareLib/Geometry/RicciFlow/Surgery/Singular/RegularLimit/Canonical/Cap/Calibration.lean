import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Supremum

/-!
# Persistence of cap-ball scalar calibration on the captured carrier

Transport an actual old cap ball into the regular region by the exact
reference map. Its scalar supremum equals the frozen inverse-square core
radius. Compact capture therefore controls its terminal scalar supremum with
an error tending to zero, uniformly over all such captured cap balls.

This estimate concerns the transported old ball. Constructing an exactly
calibrated ball for the terminal metric requires a further distance argument.
Reference: Morgan--Tian, Definition 9.72(6), pp. 230--231, and
Lemma 11.24, pp. 281--284.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareMT.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

/-- A subset of an old slice pulled back into the full regular region. -/
def regularReferencePreimage (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T)
    (S : Set (F.slice t).carrier) : Set (H.regularRegion P04) :=
  (fun x : H.regularRegion P04 => H.reference.forward t ht x) ⁻¹' S

/-- Scalar suprema on captured old sets are unchanged by the reference pullback. -/
theorem scalar_sup_regularReferencePreimage (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T)
    (S : Set (F.slice t).carrier)
    (hregular : H.reference.inverse t ht '' S ⊆ H.reference.regularLimitSet) :
    sSup (range (fun x : H.regularReferencePreimage P04 t ht S =>
      H.reference.scalar t (x : H.regularRegion P04))) =
      scalarCurvatureSupOn (F.metric t) (F.connection t) S := by
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨H.reference.forward t ht (x : H.regularRegion P04), x.property⟩,
      H.reference.scalar_pullback t ht (x : H.regularRegion P04)⟩
  · rintro ⟨y, rfl⟩
    let x : H.regularRegion P04 :=
      ⟨H.reference.inverse t ht y, hregular ⟨y, y.property, rfl⟩⟩
    have hx : x ∈ H.regularReferencePreimage P04 t ht S := by
      change H.reference.forward t ht (H.reference.inverse t ht y) ∈ S
      exact (H.reference.right_inverse t ht y).symm ▸ y.property
    refine ⟨⟨x, hx⟩, ?_⟩
    exact (H.reference.scalar_pullback t ht (H.reference.inverse t ht y)).symm.trans
      (congrArg (F.connection t).scalarCurvature (H.reference.right_inverse t ht y))

/-- Captured old sets pull back into the corresponding compact regular set. -/
theorem regularReferencePreimage_subset (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T)
    (S : Set (F.slice t).carrier) {A : Set (H.regularRegion P04)}
    (hcapture : H.reference.inverse t ht '' S ⊆ Subtype.val '' A) :
    H.regularReferencePreimage P04 t ht S ⊆ A := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := hcapture
    ⟨H.reference.forward t ht x, hx, H.reference.left_inverse t ht x⟩
  have heq : a = x := Subtype.ext hax
  exact heq ▸ ha

/-- One error bound compares every captured old cap's exact inverse-square
core radius with the actual terminal scalar supremum on its transported ball. -/
theorem eventually_cap_core_calibration_close
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t), N.connection = F.connection t →
      H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
      ∀ y ∈ N.core,
        |(N.core_radius y)⁻¹ ^ 2 -
          scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04)
            (H.regularReferencePreimage P04 t ht ((F.metric t).ball y (N.core_radius y)))| < δ := by
  filter_upwards [H.eventually_scalar_suprema_close_on_subsets P04 hA hδ] with t hsup
  intro ht N hconnection hcapture y hy
  let B := (F.metric t).ball y (N.core_radius y)
  have hyB : y ∈ B := by
    change (F.metric t).edist y y < ENNReal.ofReal (N.core_radius y)
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr (N.core_radius_pos y hy)
  have hBN : B ⊆ N.carrier := fun z hz => N.core_ball_subset y hy (subset_closure hz)
  have hBcapture : H.reference.inverse t ht '' B ⊆ Subtype.val '' A :=
    (image_mono hBN).trans hcapture
  have hBregular : H.reference.inverse t ht '' B ⊆ H.reference.regularLimitSet := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := hBcapture hz
    exact a.property
  let x : H.regularRegion P04 :=
    ⟨H.reference.inverse t ht y, hBregular ⟨y, hyB, rfl⟩⟩
  have hx : x ∈ H.regularReferencePreimage P04 t ht B := by
    change H.reference.forward t ht (H.reference.inverse t ht y) ∈ B
    exact (H.reference.right_inverse t ht y).symm ▸ hyB
  have h := hsup (H.regularReferencePreimage P04 t ht B) ⟨x, hx⟩
    (H.regularReferencePreimage_subset P04 t ht B hBcapture)
  rw [H.scalar_sup_regularReferencePreimage P04 t ht B hBregular, ← hconnection,
    N.core_radius_eq y hy] at h
  exact h

end PoincareMT.SingularTimeAssumptions
