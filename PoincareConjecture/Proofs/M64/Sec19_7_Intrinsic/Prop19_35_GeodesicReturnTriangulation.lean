import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnTransverse
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GlobalInwardOrientation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnRegionTriangulation












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_geodesic_selfintersection_triangulation
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc 0 T))
    (h0 : ‖gamma 0‖ = 1)
    (hinside : ∀ x ∈ Ioc 0 T, 1 < ‖gamma x‖ ∧ ‖gamma x‖ ≤ 2)
    (hunit : ∀ x ∈ Icc 0 T, G.inner (gamma x) (deriv gamma x) (deriv gamma x) = 1)
    (hnot : ¬ InjOn gamma (Icc 0 T)) :
    ∃ (s t : ℝ) (g : ℝ → AnnulusCoordinates),
      0 < s ∧ s < t ∧ t ≤ T ∧
      (g = (fun x => gamma (s + x)) ∨ g = (fun x => gamma (t - x))) ∧
      ContDiff ℝ ∞ g ∧ G.IsGeodesicOn g (Icc 0 (t - s)) ∧
      g 0 = g (t - s) ∧ InjOn g (Ico 0 (t - s)) ∧
      (∀ x ∈ Icc 0 (t - s), G.inner (g x) (deriv g x) (deriv g x) = 1) ∧
      LinearIndependent ℝ (![deriv g 0, -deriv g (t - s)] : Fin 2 → AnnulusCoordinates) ∧
      ∃ U V : Set AnnulusCoordinates,
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
        Disjoint U V ∧ U ∪ V = (gamma '' Icc s t)ᶜ ∧
        frontier U = g '' Icc 0 (t - s) ∧ frontier V = g '' Icc 0 (t - s) ∧
        IsCompact (closure U) ∧
        (closure U ⊆ standardAnnulusDomain ∨ Metric.closedBall (0 : AnnulusCoordinates) 1 ⊆ U) ∧
        ∃ (m : ℕ) (face : Fin m → SmoothFace AnnulusCoordinates)
          (C : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
          (b : Fin m → AffineBasis (Fin 3) ℝ Plane),
          (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p) (C p).source) ∧
          (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p).symm (C p).target) ∧
          (∀ p, convexHull ℝ (range (b p)) ⊆ (C p).source) ∧
          (∀ p, (face p).carrier = C p '' convexHull ℝ (range (b p))) ∧
          (∀ p k, ((face p).boundary k).map = C p ∘
            affineChartSegment (b p (k.succAbove 0)) (b p (k.succAbove 1))) ∧
          (∀ p q, p ≠ q → (face p).carrier ∩ (face q).carrier ⊆ frontier (face p).carrier) ∧
          (∀ p q, p ≠ q →
            (∃ k l : Fin 3, (face p).carrier ∩ (face q).carrier =
                ((face p).boundary k).map '' Icc (0 : ℝ) 1 ∧
              ((face p).boundary k).map '' Icc (0 : ℝ) 1 =
                ((face q).boundary l).map '' Icc (0 : ℝ) 1) ∨
            ∃ v : Fin 3, (face p).carrier ∩ (face q).carrier ⊆ {C p (b p v)}) ∧
          (⋃ p, (face p).carrier) = closure U := by
  have hreg (x : ℝ) (hx : x ∈ Icc 0 T) : deriv gamma x ≠ 0 := by
    intro hz
    have h := hunit x hx
    simp only [hz, map_zero] at h
    norm_num at h
  obtain ⟨s, t, hs, hst, ht, hreturn, hinj, U, V, hU, hV, hpU, hpV,
      _, _, hdisj, hcover, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_regular_selfintersection_region hg hreg hnot
  have hspos : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := le_antisymm (le_of_not_gt hn) hs
    have hnorm := (hinside t ⟨by linarith, ht⟩).1
    rw [← hreturn, hs0, h0] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  let q : ℝ → AnnulusCoordinates := fun x => gamma (s + x)
  have hq : ContDiff ℝ ∞ q := hg.comp (contDiff_const.add contDiff_id)
  have hqd (x : ℝ) : deriv q x = deriv gamma (s + x) := by
    have h := ((hg.differentiable (by simp) (s + x)).hasDerivAt).scomp x
      ((hasDerivAt_id x).const_add s)
    have h' : HasDerivAt q (deriv gamma (s + x)) x := by
      simpa only [q, Function.comp_def, id_eq, one_smul] using! h
    exact h'.deriv
  have hqgeo : G.IsGeodesicOn q (Icc 0 (t - s)) := by
    have h : G.IsGeodesicOn (fun x => gamma (x + s)) (Icc 0 (t - s)) := by
      intro x hx
      apply hgeo.comp_add s
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa only [q, add_comm] using h
  have hqe : q 0 = q (t - s) := by
    simpa only [q, add_zero, show s + (t - s) = t by ring] using hreturn
  have hqi : InjOn q (Ico 0 (t - s)) := by
    intro x hx y hy heq
    have h := hinj ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ heq
    linarith
  have hqunit (x : ℝ) (hx : x ∈ Icc 0 (t - s)) :
      G.inner (q x) (deriv q x) (deriv q x) = 1 := by
    rw [hqd]
    exact hunit (s + x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hqreg (x : ℝ) (hx : x ∈ Ioo 0 (t - s)) : deriv q x ≠ 0 := by
    rw [hqd]
    exact hreg (s + x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hqind : LinearIndependent ℝ
      (![deriv q 0, -deriv q (t - s)] : Fin 2 → AnnulusCoordinates) := by
    simpa only [hqd, add_zero, show s + (t - s) = t by ring] using
      m64Intrinsic_unit_interior_return_transverse G hg hgeo hs hst ht h0
        (fun x hx => (hinside x hx).1) hunit hreturn
  have hqimage : q '' Icc 0 (t - s) = gamma '' Icc s t := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s + x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x - s, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
      change gamma (s + (x - s)) = gamma x
      congr 1
      ring
  have hqfU : frontier U = q '' Icc 0 (t - s) := hfU.trans hqimage.symm
  have hqfV : frontier V = q '' Icc 0 (t - s) := hfV.trans hqimage.symm
  obtain ⟨g, horient, hgg, hge, hgi, hgimage, hgr, hgray⟩ :=
    m64Intrinsic_exists_global_inward_orientation hq (sub_pos.mpr hst) hqe hqi hqreg
      hU hV hdisj hqfU hqfV
  have hggeo : G.IsGeodesicOn g (Icc 0 (t - s)) := by
    rcases horient with rfl | rfl
    · exact hqgeo
    · have h : G.IsGeodesicOn (fun x => q (-1 * x + (t - s))) (Icc 0 (t - s)) := by
        intro x hx
        apply hqgeo.comp_affine (-1) (t - s)
        exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have hf : (fun x => q (t - s - x)) = (fun x => q (-1 * x + (t - s))) := by
        funext x
        congr 1
        ring
      rw [hf]
      exact h
  have hgu (x : ℝ) (hx : x ∈ Icc 0 (t - s)) :
      G.inner (g x) (deriv g x) (deriv g x) = 1 := by
    rcases horient with rfl | rfl
    · exact hqunit x hx
    · rw [deriv_comp_const_sub]
      simp only [map_neg, neg_apply, neg_neg]
      exact hqunit _ ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hgiCorner : LinearIndependent ℝ
      (![deriv g 0, -deriv g (t - s)] : Fin 2 → AnnulusCoordinates) := by
    rcases horient with rfl | rfl
    · exact hqind
    · simp only [deriv_comp_const_sub, sub_zero, sub_self, neg_neg]
      convert hqind.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.swap _ _).injective using 1
      ext i
      fin_cases i <;> simp
  have hchoices : g = (fun x => gamma (s + x)) ∨ g = (fun x => gamma (t - x)) := by
    rcases horient with h | h
    · exact Or.inl h
    · right
      rw [h]
      funext x
      dsimp only [q]
      congr 1
      ring
  have hgfU : frontier U = g '' Icc 0 (t - s) := hqfU.trans hgimage.symm
  have hgfV : frontier V = g '' Icc 0 (t - s) := hqfV.trans hgimage.symm
  refine ⟨s, t, g, hspos, hst, ht, hchoices, hgg, hggeo, hge, hgi, hgu,
    hgiCorner, U, V, hU, hV, hpU, hpV, hdisj, hcover, hgfU, hgfV, hcompact, ?_, ?_⟩
  · apply m64Intrinsic_return_region_annulus_dichotomy hU hV hdisj hcover hfU hcompact
    rintro p ⟨x, hx, rfl⟩
    exact hinside x ⟨hspos.trans_le hx.1, hx.2.trans ht⟩
  · exact m64Intrinsic_exists_return_region_triangulation hgg (sub_pos.mpr hst) hge hgi hgr
      hgiCorner hU hV hdisj hgfU hgfV hcompact hgray

end PoincareConjecture
