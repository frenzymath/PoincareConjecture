import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.EventWidthTransport
import PoincareConjecture.Statements.M61Width

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture








theorem m67_based_width_transport_of_rebased_family
    {M N : Type u}
    [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace LoopAmbient N]
    [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    (q : M59SphereQuotient)
    (g₀ : RiemannianMetric 3 M) (g₁ : RiemannianMetric 3 N)
    (x : M) (y : N)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x))
    (beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N))
      (constantC1Loop y))
    (f : ContinuousMap M N) (L : M59LoopPostcomposition f)
    (hpre : M61BasedClassWidthProperties q g₀ x alpha)
    (hpost : M61BasedClassWidthProperties q g₁ y beta)
    (hfamily : ∀ F : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M)),
      M61NullFamily F → M61FamilyWidthProperties g₀ F)
    (hpostfree : ∀ F : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M)), M61NullFamily F →
      M61FreeClassWidthProperties g₁ (L.map.comp F))
    (hnull_transport : ∀ F : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M)), M61NullFamily F →
      M61NullFamily (L.map.comp F))
    (hrebased : ∀ (F : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M))), M61NullFamily F →
      M61Represents q x alpha F →
      ∃ G : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := N)),
        M61NullFamily G ∧ M61Represents q y beta G ∧
          G.Homotopic (L.map.comp F))
    (eta : ℝ) (heta : 0 < eta)
    (htransport : ∀ (F : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M))), M61NullFamily F →
      ∀ γ (Dγ : LipschitzSpanningDisk g₀ γ),
        ∃ Eγ : LipschitzSpanningDisk g₁ (L.map γ),
          Eγ.area ≤ (1 + eta) ^ 2 * Dγ.area) :
    m61BasedClassWidth q g₁ y beta ≤
      (1 + eta) ^ 2 * m61BasedClassWidth q g₀ x alpha := by
  have hfactor : 0 < (1 + eta) ^ 2 := sq_pos_of_pos (by linarith)
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let delta : ℝ := epsilon / (1 + eta) ^ 2
  have hdelta : 0 < delta := div_pos hepsilon hfactor
  obtain ⟨F, hFnull, hFrep, hFwidth⟩ := hpre.near_minimizer delta hdelta
  obtain ⟨G, hGnull, hGrep, hGhom⟩ := hrebased F hFnull hFrep
  have hLnull : M61NullFamily (L.map.comp F) := hnull_transport F hFnull
  have hfree := hpostfree F hFnull
  have hfamily_transport := m67_family_width_transport_exact g₀ g₁ F f L
    hFnull eta heta (htransport F hFnull) (hfamily F hFnull)
  have hfree_hom : m61FreeClassWidth g₁ G =
      m61FreeClassWidth g₁ (L.map.comp F) := by
    exact (hfree.homotopy_invariant G hGnull hGhom.symm).symm
  have hfree_le_family : m61FreeClassWidth g₁ (L.map.comp F) ≤
      m61FamilyWidth g₁ (L.map.comp F) := by
    exact hfree.le_member (L.map.comp F) hLnull
      (ContinuousMap.Homotopic.refl (L.map.comp F))
  have hpost_le : m61BasedClassWidth q g₁ y beta ≤
      m61FamilyWidth g₁ (L.map.comp F) := by
    rw [hpost.eq_free G hGnull hGrep, hfree_hom]
    exact hfree_le_family
  have hpre_eq : m61FamilyWidth g₀ F ≤
      m61BasedClassWidth q g₀ x alpha + delta := hFwidth.le
  have hbound : m61BasedClassWidth q g₁ y beta ≤
      (1 + eta) ^ 2 *
        (m61BasedClassWidth q g₀ x alpha + delta) := by
    calc
      m61BasedClassWidth q g₁ y beta ≤
          m61FamilyWidth g₁ (L.map.comp F) := hpost_le
      _ ≤ (1 + eta) ^ 2 * m61FamilyWidth g₀ F :=
        hfamily_transport
      _ ≤ (1 + eta) ^ 2 *
          (m61BasedClassWidth q g₀ x alpha + delta) := by
        exact mul_le_mul_of_nonneg_left hpre_eq hfactor.le
  calc
    m61BasedClassWidth q g₁ y beta ≤
        (1 + eta) ^ 2 *
          (m61BasedClassWidth q g₀ x alpha + delta) := hbound
    _ = (1 + eta) ^ 2 * m61BasedClassWidth q g₀ x alpha + epsilon := by
      dsimp [delta]
      rw [mul_add]
      field_simp

end PoincareConjecture
