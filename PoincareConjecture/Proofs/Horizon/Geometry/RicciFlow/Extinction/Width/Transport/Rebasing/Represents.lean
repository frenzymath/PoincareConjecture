import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Rebasing.SphereTransport
import PoincareConjecture.Statements.M59LoopIdentification
import PoincareConjecture.Definitions.M61Width

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology unitInterval

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m67_normalized_family_pole
    (q : M59SphereQuotient) (x : M) (Gamma : FreeTwoSphereFamily (M := M))
    (h : M59NormalizedAt q x Gamma) :
    m59FamilyMap Gamma q.pole = constantC1Loop x := by
  let z : Fin 2 → I := fun _ => 0
  have hz : z ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  have heq := Gamma.class_certificate.family_agreement z
  rw [h.2, q.boundary_collapsed z hz] at heq
  exact heq.symm.trans ((Gamma.class_certificate.boundary_const z hz).trans
    (congrArg constantC1Loop h.1))

theorem m67_normalized_family_class
    (q : M59SphereQuotient) (x : M) (Gamma : FreeTwoSphereFamily (M := M))
    (h : M59NormalizedAt q x Gamma)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (ha : familySigmaClass Gamma = ⟨x, alpha⟩) :
    Quotient.mk' (m67SphereGenLoop q (m59FamilyMap Gamma) (constantC1Loop x)
      (m67_normalized_family_pole q x Gamma h)) = alpha := by
  have hx := h.1
  subst x
  have halpha : Gamma.homotopy_class = alpha :=
    eq_of_heq (Sigma.mk.inj_iff.mp ha).2
  rw [← halpha, Gamma.class_certificate.class_eq]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro z
  change Gamma.family (q.map z) = Gamma.class_certificate.cube_representative z
  rw [Gamma.class_certificate.family_agreement, h.2]

theorem m67_represents_rebase
    (B : M59HigherBasepointTransportService.{u}) (q : M59SphereQuotient)
    (x y : M) (C : M59IdentificationCore q y)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (p : Path (constantC1Loop x) (constantC1Loop y))
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (hF : M61Represents q x alpha F) :
    M61Represents q y (M59HigherBasepointTransport.map (B.transport 2) p alpha) F := by
  obtain ⟨Gamma, hGamma, ha, hFGamma⟩ := hF
  obtain ⟨G, hG, hhom, hclass⟩ := m67_sphere_free_transport B q
    (m59FamilyMap Gamma) (m67_normalized_family_pole q x Gamma hGamma) p
  rw [m67_normalized_family_class q x Gamma hGamma alpha ha] at hclass
  obtain ⟨Delta, hDelta, hDeltaClass⟩ := C.regular_representatives
    (M59HigherBasepointTransport.map (B.transport 2) p alpha)
  refine ⟨Delta, hDelta, hDeltaClass, hFGamma.trans (hhom.trans ?_)⟩
  apply m67_sphere_homotopic_of_class_eq q G (m59FamilyMap Delta)
    (constantC1Loop y) hG (m67_normalized_family_pole q y Delta hDelta)
  exact hclass.symm.trans
    (m67_normalized_family_class q y Delta hDelta _ hDeltaClass).symm

theorem m67_represents_postcomposition
    (S : M59IdentificationSystem.{u})
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
    (f : C(M, N)) (hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (L : M59LoopPostcomposition f) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (hF : M61Represents S.quotient x alpha F) :
    M61Represents S.quotient (f x)
      (surgeryHomotopyMap L.map (L.map_based (rfl : f x = f x)) alpha)
      (L.map.comp F) := by
  obtain ⟨Gamma, hGamma, ha, hFGamma⟩ := hF
  have hx := hGamma.1
  subst x
  have halpha : Gamma.homotopy_class = alpha :=
    eq_of_heq (Sigma.mk.inj_iff.mp ha).2
  subst alpha
  obtain ⟨Delta, hfamily, hparameter, hclass⟩ :=
    S.regular_postcomposition f hsmooth L Gamma
  have hbase : Delta.basepoint = f Gamma.basepoint := congrArg Sigma.fst hclass
  have hmap : m59FamilyMap Delta = L.map.comp (m59FamilyMap Gamma) := by
    ext c
    exact hfamily c
  refine ⟨Delta, ⟨hbase, hparameter.trans hGamma.2⟩, hclass, ?_⟩
  rw [hmap]
  exact (ContinuousMap.Homotopic.refl L.map).comp hFGamma

theorem m67_represents_postcomposition_rebase
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
    (f : C(M, N)) (hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (L : M59LoopPostcomposition f) (x : M) (y : N)
    (C : M59IdentificationCore S.quotient y)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (p : Path (constantC1Loop (f x)) (constantC1Loop y))
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (hF : M61Represents S.quotient x alpha F) :
    M61Represents S.quotient y
      (M59HigherBasepointTransport.map (B.transport 2) p
        (surgeryHomotopyMap L.map (L.map_based (rfl : f x = f x)) alpha))
      (L.map.comp F) :=
  m67_represents_rebase B S.quotient (f x) y C _ p _
    (m67_represents_postcomposition S f hsmooth L x alpha F hF)

end PoincareConjecture
