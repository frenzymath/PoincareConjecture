import PoincareConjecture.Statements.M61Width
import PoincareConjecture.Statements.M59LoopIdentification










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]


theorem m61FamilyWidth_eq_legacy (g : RiemannianMetric 3 M)
    (Gamma : FreeTwoSphereFamily (M := M)) :
    m61FamilyWidth g (m59FamilyMap Gamma) = familyWidth g Gamma := rfl


theorem m61Represents_iff_homotopic {q : M59SphereQuotient} {x : M}
    (C : M59IdentificationCore q x)
    {alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    {F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    (hF : M61Represents q x alpha F)
    (G : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) :
    M61Represents q x alpha G ↔ F.Homotopic G := by
  obtain ⟨Gamma, hGamma, hclassGamma, hFGamma⟩ := hF
  constructor
  · rintro ⟨Delta, hDelta, hclassDelta, hGDelta⟩
    have hGammaDelta := (C.free_class_identification Gamma Delta hGamma hDelta).mpr
      (hclassGamma.trans hclassDelta.symm)
    exact hFGamma.trans (hGammaDelta.trans hGDelta.symm)
  · intro hFG
    exact ⟨Gamma, hGamma, hclassGamma, hFG.symm.trans hFGamma⟩


theorem m61UniqueClassLabels_from_M59 {q : M59SphereQuotient} {x : M}
    (C : M59IdentificationCore q x) : M61UniqueClassLabels q x := by
  intro F hnull
  obtain ⟨Gamma, hGamma, hFGamma⟩ := C.raw_regularization F hnull
  have seed : ∃ alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x), familySigmaClass Gamma = ⟨x, alpha⟩ := by
    have hbase := hGamma.1
    cases hbase
    exact ⟨Gamma.homotopy_class, rfl⟩
  obtain ⟨alpha, hclassGamma⟩ := seed
  refine ⟨alpha, ⟨Gamma, hGamma, hclassGamma, hFGamma⟩, ?_⟩
  rintro beta ⟨Delta, hDelta, hclassDelta, hFDelta⟩
  have hclasses := (C.free_class_identification Gamma Delta hGamma hDelta).mp
    (hFGamma.symm.trans hFDelta)
  have hlabels := hclassDelta.symm.trans (hclasses.symm.trans hclassGamma)
  exact eq_of_heq (Sigma.mk.inj hlabels).2


theorem m61BasedClassWidthRange_eq_free {q : M59SphereQuotient} {x : M}
    (C : M59IdentificationCore q x) (g : RiemannianMetric 3 M)
    {alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    {F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    (hF : M61Represents q x alpha F) :
    m61BasedClassWidthRange q g x alpha = m61FreeClassWidthRange g F := by
  ext w
  constructor
  · rintro ⟨G, hnull, hG, hwidth⟩
    exact ⟨G, hnull, (m61Represents_iff_homotopic C hF G).mp hG, hwidth⟩
  · rintro ⟨G, hnull, hFG, hwidth⟩
    exact ⟨G, hnull, (m61Represents_iff_homotopic C hF G).mpr hFG, hwidth⟩


theorem m61BasedClassWidth_from_M59 [T2Space M] [SecondCountableTopology M]
    (W : M61RawWidthCore.{u}) {q : M59SphereQuotient} {x : M}
    (C : M59IdentificationCore q x) (g : RiemannianMetric 3 M)
    (compact : IsCompact (Set.univ : Set M))
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    M61BasedClassWidthProperties q g x alpha := by
  obtain ⟨Gamma, hGamma, hclass⟩ := C.regular_representatives alpha
  let F := m59FamilyMap Gamma
  have hnull : M61NullFamily F := Gamma.null_homotopic
  have hF : M61Represents q x alpha F :=
    ⟨Gamma, hGamma, hclass, ContinuousMap.Homotopic.refl F⟩
  have hprops := W.free_class g compact F hnull
  have hrange := m61BasedClassWidthRange_eq_free C g hF
  have hwidth : m61BasedClassWidth q g x alpha = m61FreeClassWidth g F :=
    congrArg sInf hrange
  refine
    { normalized_seed := ⟨Gamma, hGamma, hclass⟩
      nonempty := hrange.symm ▸ hprops.nonempty
      bounded_below := hrange.symm ▸ hprops.bounded_below
      nonnegative := hwidth.symm ▸ hprops.nonnegative
      range_eq_free := fun _ _ hG => m61BasedClassWidthRange_eq_free C g hG
      eq_free := fun _ _ hG => congrArg sInf (m61BasedClassWidthRange_eq_free C g hG)
      near_minimizer := ?_ }
  intro epsilon hepsilon
  obtain ⟨G, hGnull, hFG, hnear⟩ := hprops.near_minimizer epsilon hepsilon
  exact ⟨G, hGnull, (m61Represents_iff_homotopic C hF G).mpr hFG,
    hwidth.symm ▸ hnear⟩

end PoincareConjecture
