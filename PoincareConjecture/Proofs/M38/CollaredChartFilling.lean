import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.CollaredDomain
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact
import PoincareConjecture.Proofs.M38.ProjectiveReverse
import PoincareConjecture.Proofs.M38.LinearCollarBall

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_ballNeighborhood_in_coordinates
    {M : Type u} [TopologicalSpace M] [ChartedSpace StandardCapSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M StandardCapSpace)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hregular : closure (interior K) = K)
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hct : c.target ⊆ e.source)
    (hfront : frontier K = range (fun z : UnitTwoSphere => c (z, 0)))
    (hside : ∀ y ∈ c.target, y ∈ K ↔ 0 ≤ (c.symm y).2) :
    ∃ b : OpenPartialHomeomorph StandardCapSpace M,
      Metric.closedBall 0 1 ⊆ b.source ∧ b.target ⊆ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = K := by
  let L := e '' K
  have hL : IsCompact L := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hLt : L ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hKs hx)
  have himage : e.IsImage K L := e.isImage_image_of_subset_source hKs
  have hLi : interior L = e '' interior K := by
    have h := himage.interior.image_eq
    rw [inter_eq_right.mpr (interior_subset.trans hKs),
      inter_eq_right.mpr (interior_subset.trans hLt)] at h
    exact h.symm
  have hLregular : closure (interior L) = L := by
    rw [hLi]
    obtain ⟨_, _, hclosure, _⟩ := e.image_region_of_isCompact_closure
      isOpen_interior (hregular.symm ▸ hK) (hregular.symm ▸ hKs)
    simpa only [hregular] using hclosure
  have hLf : frontier L = e '' frontier K := by
    have h := himage.frontier.image_eq
    rw [inter_eq_right.mpr (hK.isClosed.frontier_subset.trans hKs),
      inter_eq_right.mpr (hL.isClosed.frontier_subset.trans hLt)] at h
    exact h.symm
  let j := c.trans e
  have hjs : univ ×ˢ Ioo (-δ) δ ⊆ j.source := by
    intro z hz
    exact ⟨hcs hz, hct (c.map_source (hcs hz))⟩
  have hjf : frontier L = range (fun z : UnitTwoSphere => j (z, 0)) := by
    rw [hLf, hfront, ← range_comp]
    rfl
  have hjside (y : StandardCapSpace) (hy : y ∈ j.target) :
      y ∈ L ↔ 0 ≤ (j.symm y).2 := by
    rw [← himage.symm_apply_mem_iff hy.1]
    exact hside _ hy.2
  obtain ⟨f, hfs, _, hf, hfi, hfL⟩ :=
    M38Schoenflies.Poincare.Manifold.Schoenflies.ball_neighborhood_of_compact_collar_side
      hL hLregular j (he.comp (hc.mono inter_subset_left) inter_subset_right)
      (hci.comp (hei.mono inter_subset_left) inter_subset_right) hδ hjs hjf hjside
  let b := f.trans e.symm
  have hbs : Metric.closedBall (0 : StandardCapSpace) 1 ⊆ b.source := by
    intro x hx
    refine ⟨hfs hx, hLt ?_⟩
    rw [← hfL]
    exact mem_image_of_mem f hx
  refine ⟨b, hbs, inter_subset_left,
    hei.comp (hf.mono inter_subset_left) inter_subset_right,
    hfi.comp (he.mono inter_subset_left) inter_subset_right, ?_⟩
  change (e.symm ∘ f) '' Metric.closedBall 0 1 = K
  rw [image_comp, hfL]
  exact e.toPartialEquiv.symm_image_image_of_subset_source hKs

theorem exists_surgeryBall_of_collared_coordinate_domain
    {A : GeneralizedSliceCarrier.{u}}
    (e : OpenPartialHomeomorph A.carrier StandardCapSpace)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set A.carrier} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hregular : closure (interior K) = K)
    (c : OpenPartialHomeomorph RoundCylinderSpace A.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hct : c.target ⊆ e.source)
    (hfront : frontier K = range (fun z : UnitTwoSphere => c (z, 0)))
    (hside : ∀ y ∈ c.target, y ∈ K ↔ (c.symm y).2 ≤ 0) :
    ∃ (r : ℝ) (D : SurgeryBallEmbedding A),
      0 < r ∧ r < 1 / 2 ∧ D.closedBall = K ∧
      D.map '' Metric.ball 0 2 ⊆ e.source ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), |s| < r →
        D.map ((1 + s) • z.val) = c (z, s) := by
  let n := projectiveCollarReflection
  let j := n.toHomeomorph.toOpenPartialHomeomorph.trans c
  have hjt : j.target = c.target := by simp [j]
  have hjs : univ ×ˢ Ioo (-δ) δ ⊆ j.source := by
    intro z hz
    refine ⟨mem_univ _, hcs ?_⟩
    change (z.1, -z.2) ∈ univ ×ˢ Ioo (-δ) δ
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hj0 (z : UnitTwoSphere) : j (z, 0) = c (z, 0) := by
    change c (z, -(0 : ℝ)) = c (z, 0)
    rw [neg_zero]
  have hjfront : frontier K = range (fun z : UnitTwoSphere => j (z, 0)) := by
    simpa only [hj0] using hfront
  have hjside (y : A.carrier) (hy : y ∈ j.target) :
      y ∈ K ↔ 0 ≤ (j.symm y).2 := by
    change y ∈ K ↔ 0 ≤ -(c.symm y).2
    simpa only [neg_nonneg] using hside y (hjt ▸ hy)
  obtain ⟨b, hbs, hbt, hb, hbi, hbK⟩ := exists_ballNeighborhood_in_coordinates
    e he hei hK hKs hregular j
    (hc.comp n.contMDiff.contMDiffOn inter_subset_right)
    (n.symm.contMDiff.comp_contMDiffOn (hci.mono inter_subset_left))
    hδ hjs (hjt.symm ▸ hct) hjfront hjside
  have hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1 := by
    rw [b.image_sphere_eq_frontier hbs hbK, hfront]
    ext y
    constructor
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
      have hs0 : s = 0 := hs
      exact ⟨z, by rw [hs0]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(z, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hpositive (z : UnitTwoSphere) (s : ℝ) (hs : 0 < s) (hsδ : s < δ) :
      c (z, s) ∉ b '' Metric.closedBall 0 1 := by
    rw [hbK]
    have hzs : (z, s) ∈ c.source :=
      hcs ⟨mem_univ _, by constructor <;> linarith⟩
    intro h
    have hle := (hside _ (c.map_source hzs)).mp h
    rw [c.left_inv hzs] at hle
    exact hs.not_ge hle
  obtain ⟨r, D, hr, hrhalf, hD, hDt, hmatch⟩ :=
    exists_surgeryBall_matching_linear_collar b hbs hb hbi c hc hci
      hδ hcs hzero hpositive
  exact ⟨r, D, hr, hrhalf, hD.trans hbK, hDt.trans hbt, hmatch⟩

end PoincareConjecture.M38
