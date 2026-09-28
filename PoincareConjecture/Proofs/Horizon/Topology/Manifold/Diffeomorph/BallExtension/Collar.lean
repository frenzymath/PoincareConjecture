import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.SupportedCollar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare

open PoincareConjecture

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

theorem exists_sphere_diffeomorph_of_collar
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    (hs : univ ×ˢ ({0} : Set ℝ) ⊆ c.source)
    (hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = Metric.sphere 0 1) :
    ∃ d : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      ∀ q : UnitTwoSphere, (d q : E3) = c (q, 0) := by
  have hz (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source := hs ⟨mem_univ _, rfl⟩
  have hcs (q : UnitTwoSphere) : c (q, 0) ∈ Metric.sphere (0 : E3) 1 :=
    hzero ▸ mem_image_of_mem c ⟨mem_univ q, rfl⟩
  have hct (q : UnitTwoSphere) : (q : E3) ∈ c.target := by
    obtain ⟨p, hp, heq⟩ := hzero.symm.subset q.property
    exact heq ▸ c.map_source (hs hp)
  have hcz (q : UnitTwoSphere) : (c.symm q).2 = 0 := by
    obtain ⟨p, hp, heq⟩ := hzero.symm.subset q.property
    rw [← heq, c.left_inv (hs hp)]
    exact hp.2
  let f : UnitTwoSphere → UnitTwoSphere := fun q => ⟨c (q, 0), hcs q⟩
  let k : UnitTwoSphere → UnitTwoSphere := fun q => (c.symm q).1
  have hfk (q : UnitTwoSphere) : f (k q) = q := by
    apply Subtype.ext
    change c ((c.symm q).1, 0) = q.val
    rw [← hcz q, Prod.eta, c.right_inv (hct q)]
  have hkf (q : UnitTwoSphere) : k (f q) = q := by
    change (c.symm (c (q, 0))).1 = q
    rw [c.left_inv (hz q)]
  have hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f := by
    apply ContMDiff.codRestrict_sphere (f := fun q : UnitTwoSphere => c (q, 0))
    intro q
    exact (hc.contMDiffAt (c.open_source.mem_nhds (hz q))).comp q
      (contMDiff_id.prodMk contMDiff_const q)
  have hk : ContMDiff (𝓡 2) (𝓡 2) ∞ k := by
    intro q
    exact contMDiffAt_fst.comp q
      ((hci.contMDiffAt (c.open_target.mem_nhds (hct q))).comp q
        (contMDiff_coe_sphere q))
  exact ⟨{
    toFun := f
    invFun := k
    left_inv := hkf
    right_inv := hfk
    contMDiff_toFun := hf
    contMDiff_invFun := hk }, fun _ => rfl⟩

theorem exists_ambient_extension_of_sphere_collar
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = Metric.sphere 0 1)
    (hpositive : ∀ (q : UnitTwoSphere) (t : ℝ), 0 < t → t < δ → 1 < ‖c (q, t)‖) :
    ∃ (η : ℝ) (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ η < δ ∧ F '' Metric.closedBall 0 1 = Metric.closedBall 0 1 ∧
      ∀ p : RoundCylinderSpace, |p.2| < η → F (Real.exp p.2 • (p.1 : E3)) = c p := by
  have hz : univ ×ˢ ({0} : Set ℝ) ⊆ c.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hsource ⟨mem_univ _, by constructor <;> linarith⟩
  obtain ⟨d, hd⟩ := exists_sphere_diffeomorph_of_collar c hc hci hz hzero
  obtain ⟨A, hAball, r, hr, _, hA⟩ := Manifold.exists_sphere_diffeomorph_extension d
  have hAq (q : UnitTwoSphere) : A q = c (q, 0) := by
    have h : A q = (d q : E3) := by
      simpa using hA q 1 (by constructor <;> linarith)
    exact h.trans (hd q)
  let e := c.trans A.symm.toHomeomorph.toOpenPartialHomeomorph
  have hes : e.source = c.source := by simp [e]
  have heq (p : RoundCylinderSpace) : e p = A.symm (c p) := rfl
  have hezero (q : UnitTwoSphere) : e (q, 0) = (q : E3) := by
    rw [heq, ← hAq, A.symm_apply_apply]
  have hepos (q : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
      1 < ‖e (q, t)‖ := by
    by_contra hn
    have hmem : A.symm (c (q, t)) ∈ Metric.closedBall (0 : E3) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, ← heq] using le_of_not_gt hn
    have himage := hAball ▸ mem_image_of_mem A hmem
    rw [A.apply_symm_apply] at himage
    have hle : ‖c (q, t)‖ ≤ 1 := by simpa using himage
    exact (not_le_of_gt (hpositive q t ht htδ)) hle
  have he : ContMDiffOn CylModel (𝓡 3) ∞ e e.source := by
    rw [hes]
    exact A.symm.contMDiff.comp_contMDiffOn hc
  have hei : ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target :=
    hci.comp A.contMDiff.contMDiffOn inter_subset_right
  obtain ⟨η, B, hη, hηδ, _, hBball, hB, _⟩ :=
    exists_ambient_extension_of_outward_sphere_collar e he hei hδ (hes ▸ hsource)
      hezero hepos δ hδ
  refine ⟨η, B.trans A, hη, hηδ, ?_, ?_⟩
  · change (A ∘ B) '' Metric.closedBall 0 1 = Metric.closedBall 0 1
    calc
      (A ∘ B) '' Metric.closedBall 0 1 = A '' (B '' Metric.closedBall 0 1) :=
        (image_image (⇑A) (⇑B) (Metric.closedBall 0 1)).symm
      _ = Metric.closedBall 0 1 := by rw [hBball, hAball]
  · intro p hp
    change A (B (Real.exp p.2 • (p.1 : E3))) = c p
    rw [hB p hp, heq, A.apply_symm_apply]

theorem exists_ball_neighborhood_matching_collar
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (b : OpenPartialHomeomorph E3 M)
    (hbs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (htarget : c '' (univ ×ˢ Ioo (-δ) δ) ⊆ b.target)
    (hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1)
    (hpositive : ∀ (q : UnitTwoSphere) (t : ℝ), 0 < t → t < δ →
      c (q, t) ∉ b '' Metric.closedBall 0 1) :
    ∃ (η : ℝ) (a : OpenPartialHomeomorph E3 M),
      0 < η ∧ η < δ ∧ Metric.closedBall 0 1 ⊆ a.source ∧
      a.target = b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ a a.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ a.symm a.target ∧
      a '' Metric.closedBall 0 1 = b '' Metric.closedBall 0 1 ∧
      ∀ p : RoundCylinderSpace, |p.2| < η →
        Real.exp p.2 • (p.1 : E3) ∈ a.source ∧
        a (Real.exp p.2 • (p.1 : E3)) = c p := by
  let e := c.trans b.symm
  have hes : univ ×ˢ Ioo (-δ) δ ⊆ e.source := by
    intro p hp
    exact ⟨hsource hp, htarget (mem_image_of_mem c hp)⟩
  have he : ContMDiffOn CylModel (𝓡 3) ∞ e e.source :=
    hbi.comp (hc.mono inter_subset_left) inter_subset_right
  have hei : ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target :=
    hci.comp (hb.mono inter_subset_left) inter_subset_right
  have hezero : e '' (univ ×ˢ ({0} : Set ℝ)) = Metric.sphere 0 1 := by
    change (b.symm ∘ c) '' (univ ×ˢ ({0} : Set ℝ)) = Metric.sphere 0 1
    calc
      (b.symm ∘ c) '' (univ ×ˢ ({0} : Set ℝ)) =
          b.symm '' (c '' (univ ×ˢ ({0} : Set ℝ))) :=
        (image_image (⇑b.symm) (⇑c) _).symm
      _ = b.symm '' (b '' Metric.sphere 0 1) := by rw [hzero]
      _ = Metric.sphere 0 1 := b.toPartialEquiv.symm_image_image_of_subset_source
        (Metric.sphere_subset_closedBall.trans hbs)
  have hepositive (q : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
      1 < ‖e (q, t)‖ := by
    have hp : (q, t) ∈ univ ×ˢ Ioo (-δ) δ :=
      ⟨mem_univ _, by constructor <;> linarith⟩
    by_contra hn
    have hmem : e (q, t) ∈ Metric.closedBall (0 : E3) 1 := by
      simpa using le_of_not_gt hn
    apply hpositive q t ht htδ
    refine ⟨e (q, t), hmem, ?_⟩
    exact b.right_inv (htarget (mem_image_of_mem c hp))
  obtain ⟨η, F, hη, hηδ, hFball, hF⟩ :=
    exists_ambient_extension_of_sphere_collar e he hei hδ hes hezero hepositive
  let a := F.toHomeomorph.toOpenPartialHomeomorph.trans b
  have has : Metric.closedBall (0 : E3) 1 ⊆ a.source := by
    intro x hx
    exact ⟨mem_univ _, hbs (hFball ▸ mem_image_of_mem F hx)⟩
  refine ⟨η, a, hη, hηδ, has, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a]
  · exact hb.comp F.contMDiff.contMDiffOn inter_subset_right
  · exact F.symm.contMDiff.comp_contMDiffOn (hbi.mono inter_subset_left)
  · change (b ∘ F) '' Metric.closedBall 0 1 = b '' Metric.closedBall 0 1
    calc
      (b ∘ F) '' Metric.closedBall 0 1 = b '' (F '' Metric.closedBall 0 1) :=
        (image_image (⇑b) (⇑F) _).symm
      _ = b '' Metric.closedBall 0 1 := by rw [hFball]
  · intro p hp
    have hpδ : p ∈ univ ×ˢ Ioo (-δ) δ := ⟨mem_univ _, abs_lt.mp (hp.trans hηδ)⟩
    have hcpt := htarget (mem_image_of_mem c hpδ)
    have hFp : F (Real.exp p.2 • (p.1 : E3)) = b.symm (c p) := hF p hp
    constructor
    · refine ⟨mem_univ _, ?_⟩
      change F (Real.exp p.2 • (p.1 : E3)) ∈ b.source
      rw [hFp]
      exact b.map_target hcpt
    · change b (F (Real.exp p.2 • (p.1 : E3))) = c p
      rw [hFp, b.right_inv hcpt]

end Poincare
