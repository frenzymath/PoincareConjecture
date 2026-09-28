import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.ChartLinearization
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace Poincare.Manifold.SphereIsotopy

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := PoincareConjecture.UnitTwoSphere

def centeredChart (p : S2) : OpenPartialHomeomorph S2 E2 := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  exact stereographic' 2 (-p)

@[simp] theorem centeredChart_source (p : S2) :
    (centeredChart p).source = {-p}ᶜ := by
  simp [centeredChart]

@[simp] theorem centeredChart_target (p : S2) :
    (centeredChart p).target = univ := by
  simp [centeredChart]

theorem centeredChart_mem_maximalAtlas (p : S2) :
    centeredChart p ∈ maximalAtlas (𝓡 2) ∞ S2 := by
  apply IsManifold.subset_maximalAtlas
  exact ⟨-p, rfl⟩

@[simp] theorem centeredChart_apply_center (p : S2) : centeredChart p p = 0 := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have h (q : S2) : stereographic' 2 q (-q) = 0 := by
    simp [stereographic', stereographic_apply_neg]
  simpa only [centeredChart, neg_neg] using h (-p)

@[simp] theorem centeredChart_symm_zero (p : S2) : (centeredChart p).symm 0 = p := by
  have hp : p ∈ (centeredChart p).source := by
    simpa using ne_neg_of_mem_unit_sphere ℝ p
  simpa only [centeredChart_apply_center] using (centeredChart p).left_inv hp

theorem exists_local_linearization
    (d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) (p : S2) :
    ∃ r : ℝ, 0 < r ∧ ∃ L : E2 ≃L[ℝ] E2,
      ∃ K : Set S2, IsCompact K ∧ K ⊆ {-d p}ᶜ ∧
      ∃ Φ : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
      (∀ q, Φ 0 q = q) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun z : ℝ × S2 => Φ z.1 z.2) ∧
      (∀ t q, q ∉ K → Φ t q = q) ∧
      ∀ x ∈ closedBall (0 : E2) r,
        Φ 1 (d ((centeredChart p).symm x)) = (centeredChart (d p)).symm (L x) := by
  let c := centeredChart p
  let b := centeredChart (d p)
  let e := c.symm.trans d.toHomeomorph.toOpenPartialHomeomorph
  have hc := centeredChart_mem_maximalAtlas p
  have hb := centeredChart_mem_maximalAtlas (d p)
  have he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source := by
    change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun x => d (c.symm x)) e.source
    exact d.contMDiff.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono inter_subset_left)
  have hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun x => c (d.symm x)) e.target
    exact (contMDiffOn_of_mem_maximalAtlas hc).comp
      d.symm.contMDiff.contMDiffOn inter_subset_right
  obtain ⟨r, hr, L, K, hK, hKb, Φ, hΦ0, hΦs, hΦfix, _, hΦ⟩ :=
    Schoenflies.exists_supported_chart_linearization e b.symm he hei
      (contMDiffOn_symm_of_mem_maximalAtlas hb)
      (contMDiffOn_of_mem_maximalAtlas hb)
      (by simp [e, c])
      (by simp [b]) (by simp [e, c, b])
  exact ⟨r, hr, L, K, hK, by simpa [b] using hKb, Φ, hΦ0, hΦs, hΦfix, hΦ⟩

end Poincare.Manifold.SphereIsotopy
