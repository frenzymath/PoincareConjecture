import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set PoincareConjecture TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem ball_neighborhood_matching_collar_in_coordinates
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (e : OpenPartialHomeomorph M E3) (het : e.target = univ)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hregular : closure (interior K) = K)
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hct : c.target ⊆ e.source)
    (hfront : frontier K = range (fun q : UnitTwoSphere => c (q, 0)))
    (hside : ∀ y ∈ c.target, y ∈ K ↔ (c.symm y).2 ≤ 0) :
    ∃ (r : ℝ) (b : OpenPartialHomeomorph E3 M),
      0 < r ∧ r < δ ∧ Metric.closedBall 0 1 ⊆ b.source ∧ b.target ⊆ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = K ∧
      ∀ z : RoundCylinderSpace, |z.2| < r →
        Real.exp z.2 • (z.1 : E3) ∈ b.source ∧
        b (Real.exp z.2 • (z.1 : E3)) = c z := by
  let R : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
    toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
    contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
    contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
  let d := R.toHomeomorph.toOpenPartialHomeomorph.trans c
  have hdt : d.target = c.target := by simp [d]
  have hd0 (q : UnitTwoSphere) : d (q, 0) = c (q, 0) := by
    change c (q, -(0 : ℝ)) = c (q, 0)
    rw [neg_zero]
  have hds : univ ×ˢ Ioo (-δ) δ ⊆ d.source := by
    intro z hz
    refine ⟨mem_univ _, hcs ?_⟩
    change (z.1, -z.2) ∈ univ ×ˢ Ioo (-δ) δ
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hdf : frontier K = range (fun q : UnitTwoSphere => d (q, 0)) := by
    simpa only [hd0] using hfront
  have hdside (y : M) (hy : y ∈ d.target) : y ∈ K ↔ 0 ≤ (d.symm y).2 := by
    change y ∈ K ↔ 0 ≤ -(c.symm y).2
    rw [neg_nonneg]
    exact hside y (hdt ▸ hy)
  obtain ⟨v, hvs, hvt, hv, hvi, hvK⟩ := ball_neighborhood_in_coordinates e het he hei
    hK hKs hregular d (hc.comp R.contMDiff.contMDiffOn inter_subset_right)
    (R.symm.contMDiff.comp_contMDiffOn (hci.mono inter_subset_left)) hδ hds
    (hdt.symm ▸ hct) hdf hdside
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source :=
    hcs ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hcv : c '' (univ ×ˢ ({0} : Set ℝ)) = v '' Metric.sphere 0 1 := by
    rw [v.image_sphere_eq_frontier hvs hvK, hfront]
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  let W : Opens RoundCylinderSpace := ⟨(c.trans v.symm).source ∩ (univ ×ˢ Ioo (-δ) δ),
    (c.trans v.symm).open_source.inter (isOpen_univ.prod isOpen_Ioo)⟩
  have hzeroW (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ W := by
    refine ⟨⟨hzero q, ?_⟩, mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
    obtain ⟨x, hx, hxq⟩ := hcv.subset
      (mem_image_of_mem c (show (q, (0 : ℝ)) ∈ univ ×ˢ ({0} : Set ℝ) from ⟨mem_univ _, rfl⟩))
    change c (q, 0) ∈ v.target
    exact hxq ▸ v.map_source (hvs (Metric.sphere_subset_closedBall hx))
  obtain ⟨η, hη, hηW⟩ := CylinderGluing.exists_cylinder_collar W hzeroW
  let ε := min η δ
  have hε : 0 < ε := lt_min hη hδ
  have hεs : univ ×ˢ Ioo (-ε) ε ⊆ c.source := by
    intro z hz
    exact (hηW z ((abs_lt.mpr hz.2).trans_le (min_le_left _ _))).1.1
  have hεv : c '' (univ ×ˢ Ioo (-ε) ε) ⊆ v.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hηW z ((abs_lt.mpr hz.2).trans_le (min_le_left _ _))).1.2
  have hpositive (q : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (hte : t < ε) :
      c (q, t) ∉ v '' Metric.closedBall 0 1 := by
    rw [hvK]
    have hz : (q, t) ∈ c.source := hεs ⟨mem_univ _, by constructor <;> linarith⟩
    intro hcK
    have h := (hside _ (c.map_source hz)).mp hcK
    rw [c.left_inv hz] at h
    exact (not_le_of_gt ht) h
  obtain ⟨r, b, hr, hre, hbs, hbt, hb, hbi, hbK, hmatch⟩ :=
    Poincare.exists_ball_neighborhood_matching_collar v hvs hv hvi c hc hci hε hεs hεv hcv hpositive
  exact ⟨r, b, hr, hre.trans_le (min_le_right _ _), hbs, hbt ▸ hvt, hb, hbi,
    hbK.trans hvK, hmatch⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
