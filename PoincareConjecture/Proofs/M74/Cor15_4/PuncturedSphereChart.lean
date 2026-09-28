import PoincareConjecture.Definitions.M74ConnectedSumReduction

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

noncomputable def punctureChart : OpenPartialHomeomorph A.carrier StandardCapSpace :=
  d.toHomeomorph.toOpenPartialHomeomorph.trans
    (chartAt StandardCapSpace (-(d (B.map 0))))

private theorem sphere_chart_source (p : ThreeSphere) :
    (chartAt StandardCapSpace (-p)).source = {p}ᶜ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  change (stereographic' 3 (- -p)).source = {p}ᶜ
  simp

private theorem sphere_chart_target (p : ThreeSphere) :
    (chartAt StandardCapSpace (-p)).target = univ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  change (stereographic' 3 (- -p)).target = univ
  simp

@[simp] theorem punctureChart_source : (B.punctureChart d).source = {B.map 0}ᶜ := by
  ext x
  simp [punctureChart, sphere_chart_source]

@[simp] theorem punctureChart_target : (B.punctureChart d).target = univ := by
  simp [punctureChart, sphere_chart_target]

theorem punctureChart_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (B.punctureChart d) (B.punctureChart d).source := by
  apply contMDiffOn_chart.comp d.contMDiff.contMDiffOn
  intro x hx
  exact hx.2

theorem punctureChart_symm_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (B.punctureChart d).symm := by
  apply contMDiffOn_univ.mp
  change ContMDiffOn (𝓡 3) (𝓡 3) ∞
    (d.symm ∘ (chartAt StandardCapSpace (-(d (B.map 0)))).symm) univ
  apply d.symm.contMDiff.comp_contMDiffOn
  rw [← sphere_chart_target (d (B.map 0))]
  exact contMDiffOn_chart_symm

theorem closedBall_compl_subset_punctureChart_source :
    B.closedBallᶜ ⊆ (B.punctureChart d).source := by
  rw [B.punctureChart_source d]
  intro x hx hxp
  have hcenter : B.map 0 ∈ B.closedBall := mem_image_of_mem _ (by simp)
  exact hx (mem_singleton_iff.mp hxp ▸ hcenter)

theorem map_mem_punctureChart_source_iff {x : StandardCapSpace}
    (hx : x ∈ ball 0 2) : B.map x ∈ (B.punctureChart d).source ↔ x ≠ 0 := by
  rw [B.punctureChart_source d]
  simp only [mem_compl_iff, mem_singleton_iff]
  exact not_congr ⟨fun h => B.left_inverse.injOn hx (by simp) h, congrArg B.map⟩

theorem map_ball_isOpen {r : ℝ} (hr : r ≤ 2) :
    IsOpen (B.map '' ball (0 : StandardCapSpace) r) := by
  have himage : (fun x : ball (0 : StandardCapSpace) 2 => B.map x.1) ''
      (Subtype.val ⁻¹' ball (0 : StandardCapSpace) r) =
      B.map '' ball (0 : StandardCapSpace) r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_image_of_mem _ hx
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, ball_subset_ball hr hx⟩, hx, rfl⟩
  rw [← himage]
  exact B.open_embedding.isOpenMap _ (isOpen_ball.preimage continuous_subtype_val)

theorem map_ball_compl_subset_punctureChart_source {r : ℝ} (hr : 0 < r) :
    (B.map '' ball (0 : StandardCapSpace) r)ᶜ ⊆ (B.punctureChart d).source := by
  rw [B.punctureChart_source d]
  intro x hx hxp
  have hcenter : B.map 0 ∈ B.map '' ball (0 : StandardCapSpace) r :=
    mem_image_of_mem _ (mem_ball_self hr)
  exact hx (mem_singleton_iff.mp hxp ▸ hcenter)

theorem punctureChart_image_exterior_isCompact {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    IsCompact ((B.punctureChart d) '' (B.map '' ball (0 : StandardCapSpace) r)ᶜ) := by
  let : CompactSpace A.carrier := d.toHomeomorph.symm.compactSpace
  exact (B.map_ball_isOpen hr2).isClosed_compl.isCompact.image_of_continuousOn
    ((B.punctureChart d).continuousOn.mono
      (B.map_ball_compl_subset_punctureChart_source d hr))

theorem exterior_image_compl_subset_punctured_image (r : ℝ) :
    ((B.punctureChart d) '' (B.map '' ball (0 : StandardCapSpace) r)ᶜ)ᶜ ⊆
      (B.punctureChart d) '' ((B.map '' ball (0 : StandardCapSpace) r) \ {B.map 0}) := by
  intro y hy
  have hyt : y ∈ (B.punctureChart d).target := by simp
  have hxs := (B.punctureChart d).map_target hyt
  have hxy := (B.punctureChart d).right_inv hyt
  have hxball : (B.punctureChart d).symm y ∈ B.map '' ball (0 : StandardCapSpace) r := by
    by_contra hx
    exact hy ⟨(B.punctureChart d).symm y, hx, hxy⟩
  exact ⟨(B.punctureChart d).symm y,
    ⟨hxball, by simpa only [B.punctureChart_source d, mem_compl_iff] using hxs⟩, hxy⟩

theorem punctureChart_image_puncturedBall_unbounded {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ¬Bornology.IsBounded ((B.punctureChart d) ''
      ((B.map '' ball (0 : StandardCapSpace) r) \ {B.map 0})) := by
  intro hbounded
  apply NormedSpace.unbounded_univ ℝ StandardCapSpace
  apply ((B.punctureChart_image_exterior_isCompact d hr hr2).isBounded.union hbounded).subset
  intro y _
  by_cases hy : y ∈ (B.punctureChart d) '' (B.map '' ball (0 : StandardCapSpace) r)ᶜ
  · exact Or.inl hy
  · exact Or.inr (B.exterior_image_compl_subset_punctured_image d r hy)

end PoincareConjecture.SurgeryBallEmbedding
