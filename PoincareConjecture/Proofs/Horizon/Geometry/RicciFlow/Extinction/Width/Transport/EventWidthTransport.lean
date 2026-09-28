import PoincareConjecture.Definitions.M67
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskExistence
import PoincareConjecture.Statements.M61Width
import PoincareConjecture.Proofs.M61.Def18_17_Width.SphereCompactness

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N]
  [IsManifold (𝓡 3) ∞ N]
  [T2Space N] [SecondCountableTopology N]

theorem m67_family_width_transport
    (g₀ : RiemannianMetric 3 M) (g₁ : RiemannianMetric 3 N)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (f : ContinuousMap M N) (L : M59LoopPostcomposition f)
    (hnull : M61NullFamily F)
    (eta : ℝ) (heta : 0 < eta)
    (htransport : ∀ γ (Dγ : LipschitzSpanningDisk g₀ γ),
      ∃ Eγ : LipschitzSpanningDisk g₁ (L.map γ),
        Eγ.area ≤ (1 + eta) ^ 2 * Dγ.area)
    (hwidth : M61FamilyWidthProperties g₀ F) :
    ∀ epsilon : ℝ, 0 < epsilon →
      m61FamilyWidth g₁ (L.map.comp F) ≤
        (1 + eta) ^ 2 * (m61FamilyWidth g₀ F + epsilon) := by
  letI : Nonempty LoopTwoSphere := PoincareConjecture.Proofs.M61.loopTwoSphereNonempty
  intro epsilon hepsilon
  have hfactor : 0 < (1 + eta) ^ 2 := sq_pos_of_pos (by linarith)
  have hpoint : ∀ c : LoopTwoSphere,
      fillingArea g₁ (L.map (F c)) ≤
        (1 + eta) ^ 2 * (fillingArea g₀ (F c) + epsilon) := by
    intro c
    obtain ⟨D₀⟩ := m60_exists_lipschitz_disk_of_null g₀ (F c) (hnull c)
    obtain ⟨D, hD⟩ := m60FillingArea_near_minimizer_of_disk g₀ (F c) D₀ hepsilon
    obtain ⟨E, hE⟩ := htransport (F c) D
    have hfill : fillingArea g₁ (L.map (F c)) ≤ E.area :=
      m60FillingArea_le_disk g₁ (L.map (F c)) E
    have hmul : (1 + eta) ^ 2 * D.area <
        (1 + eta) ^ 2 * (fillingArea g₀ (F c) + epsilon) :=
      mul_lt_mul_of_pos_left hD hfactor
    exact hfill.trans (hE.trans hmul.le)
  unfold m61FamilyWidth
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨c, rfl⟩
    have hpre : fillingArea g₀ (F c) ≤ m61FamilyWidth g₀ F := by
      unfold m61FamilyWidth
      exact le_csSup hwidth.bounded_above ⟨c, rfl⟩
    have hpre' : fillingArea g₀ (F c) ≤
        sSup (Set.range (fun c => fillingArea g₀ (F c))) := by
      simpa only [m61FamilyWidth] using hpre
    exact (hpoint c).trans (mul_le_mul_of_nonneg_left
      (add_le_add_left hpre' epsilon) hfactor.le)

theorem m67_family_width_transport_exact
    (g₀ : RiemannianMetric 3 M) (g₁ : RiemannianMetric 3 N)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (f : ContinuousMap M N) (L : M59LoopPostcomposition f)
    (hnull : M61NullFamily F)
    (eta : ℝ) (heta : 0 < eta)
    (htransport : ∀ γ (Dγ : LipschitzSpanningDisk g₀ γ),
      ∃ Eγ : LipschitzSpanningDisk g₁ (L.map γ),
        Eγ.area ≤ (1 + eta) ^ 2 * Dγ.area)
    (hwidth : M61FamilyWidthProperties g₀ F) :
    m61FamilyWidth g₁ (L.map.comp F) ≤
      (1 + eta) ^ 2 * m61FamilyWidth g₀ F := by
  have hfactor : 0 < (1 + eta) ^ 2 := sq_pos_of_pos (by linarith)
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have hε : 0 < epsilon / (1 + eta) ^ 2 := div_pos hepsilon hfactor
  have h := m67_family_width_transport g₀ g₁ F f L hnull eta heta
    htransport hwidth (epsilon / (1 + eta) ^ 2) hε
  have hfactor_ne : (1 + eta) ^ 2 ≠ 0 := ne_of_gt hfactor
  calc
    m61FamilyWidth g₁ (L.map.comp F) ≤
        (1 + eta) ^ 2 *
          (m61FamilyWidth g₀ F + epsilon / (1 + eta) ^ 2) := h
    _ = (1 + eta) ^ 2 * m61FamilyWidth g₀ F + epsilon := by
      rw [mul_add, mul_div_cancel₀ _ hfactor_ne]

end PoincareConjecture
