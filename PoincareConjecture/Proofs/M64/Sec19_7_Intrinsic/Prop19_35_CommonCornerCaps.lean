import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FittedCornerCap
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Coordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Triangles PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_corner_faces_at_scale
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target) :
    ∃ rho > 0, ∀ r : ℝ, 0 < r → r < rho →
      ∃ (face : SmoothFace AnnulusCoordinates) (W : Set AnnulusCoordinates),
        face.carrier ⊆ H '' (H.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 1).map t = H (0, t * r)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 2).map t = H (t * r, 0)) ∧
        (∀ t : ℝ, (face.boundary 0).map t =
          (1 - t) • H (r, 0) + t • H (0, r)) ∧
        H (r, 0) ≠ H (0, r) ∧
        IsOpen W ∧ H 0 ∈ W ∧ W ⊆ H.target ∧
        W ∩ H '' (H.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ⊆ face.carrier ∧
        ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
          (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
          convexHull ℝ (range b) ⊆ C.source ∧
          face.carrier = C '' convexHull ℝ (range b) ∧
          ∀ k, (face.boundary k).map = C ∘
            affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) := by
  obtain ⟨rho, hrho, hcaps⟩ := exists_smooth_coordinate_corner_caps H h0 hH hHi
  refine ⟨rho, hrho, ?_⟩
  intro r hr hrrho
  obtain ⟨F, hsource, _, hF, hFi, hfirst, hsecond, hchord, _, hsub,
      W, hW, hpW, hWt, hcover⟩ := hcaps r hr hrrho
  let C := collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans F
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    contMDiffOn_iff_contDiffOn.mpr
      (hF.comp collarParameterEquiv.contDiff.contDiffOn (fun _ hz => hz.2))
  have hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    contMDiffOn_iff_contDiffOn.mpr
      (collarParameterEquiv.symm.contDiff.comp_contDiffOn (hFi.mono (fun _ hz => hz.1)))
  have htriangle : convexHull ℝ (range (rightTriangleBasis hr)) ⊆ C.source := by
    intro z hz
    exact ⟨mem_univ _, hsource ((mem_rightTriangleBasis_convexHull hr z).mp hz)⟩
  obtain ⟨face, _, _, hcarrier, _, hboundary⟩ :=
    exists_smoothFace_of_smooth_coordinates C hC hCi (rightTriangleBasis hr) htriangle
      (0 : AnnulusCoordinates) (by intro z _; simp)
  have hface : face.carrier =
      F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
    rw [hcarrier]
    ext z
    constructor
    · rintro ⟨q, hq, heq⟩
      exact ⟨collarParameterEquiv q, (mem_rightTriangleBasis_convexHull hr q).mp hq, heq⟩
    · rintro ⟨q, hq, heq⟩
      refine ⟨collarParameterEquiv.symm q,
        (mem_rightTriangleBasis_convexHull hr _).mpr hq, ?_⟩
      change F (collarParameterEquiv (collarParameterEquiv.symm q)) = z
      rwa [collarParameterEquiv.apply_symm_apply]
  have ht {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |t * r| < rho := by
    rw [abs_of_nonneg (mul_nonneg ht.1 hr.le)]
    exact ((mul_le_mul_of_nonneg_right ht.2 hr.le).trans_eq (one_mul r)).trans_lt hrrho
  refine ⟨face, W, hface ▸ hsub, ?_, ?_, ?_, ?_, hW, hpW, hWt, hface ▸ hcover,
    C, rightTriangleBasis hr, hC, hCi, htriangle, hcarrier, hboundary⟩
  · intro t ht'
    rw [hboundary]
    change F (collarParameterEquiv
      (affineChartSegment (rightTriangleBasis hr 0) (rightTriangleBasis hr 2) t)) = _
    simpa [affineChartSegment, rightTriangleBasis_apply, collarParameterEquiv, mul_comm]
      using hsecond (t * r) (ht ht')
  · intro t ht'
    rw [hboundary]
    rw [show Fin.succAbove (2 : Fin 3) 1 = 1 by decide]
    change F (collarParameterEquiv
      (affineChartSegment (rightTriangleBasis hr 0) (rightTriangleBasis hr 1) t)) = _
    simpa [affineChartSegment, rightTriangleBasis_apply, collarParameterEquiv, mul_comm]
      using hfirst (t * r) (ht ht')
  · intro t
    rw [hboundary]
    have he : collarParameterEquiv
        (affineChartSegment (rightTriangleBasis hr 1) (rightTriangleBasis hr 2) t) =
        ((1 - t) * r, t * r) := by
      ext <;> simp [affineChartSegment, rightTriangleBasis_apply, collarParameterEquiv]
      ring
    change F (collarParameterEquiv
      (affineChartSegment (rightTriangleBasis hr 1) (rightTriangleBasis hr 2) t)) = _
    rw [he]
    have hc := hchord (1 - t)
    rw [show 1 - (1 - t) = t by ring, add_comm] at hc
    exact hc
  · intro heq
    have hsmall : |r| < rho := by rwa [abs_of_pos hr]
    have heq' := F.injOn (hsource ⟨hr.le, le_rfl, by simp⟩)
      (hsource ⟨le_rfl, hr.le, by simp⟩)
      ((hfirst r hsmall).trans (heq.trans (hsecond r hsmall).symm))
    exact hr.ne' (congrArg Prod.fst heq')

theorem m64Intrinsic_exists_four_corner_faces
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {T : ℝ} (hT : 0 < T) :
    ∃ (r : ℝ) (face : Bool × Bool → SmoothFace AnnulusCoordinates)
      (W : Set AnnulusCoordinates),
      0 < r ∧ r ≤ T ∧ IsOpen W ∧ H 0 ∈ W ∧ W ⊆ H.target ∧
      (∀ i, (face i).carrier ⊆ H '' (H.source ∩
        (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})) ∧
      (∀ i, W ∩ H '' (H.source ∩
        (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ⊆
        (face i).carrier) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 1).map t =
        H (sectorParameterEquiv 0 i (0, t * r))) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 2).map t =
        H (sectorParameterEquiv 0 i (t * r, 0))) ∧
      (∀ i t, ((face i).boundary 0).map t =
        (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
          t • H (sectorParameterEquiv 0 i (0, r))) ∧
      (∀ i, H (sectorParameterEquiv 0 i (r, 0)) ≠
        H (sectorParameterEquiv 0 i (0, r))) ∧
      (∀ i j, i.1 = j.1 → EqOn ((face i).boundary 2).map
        ((face j).boundary 2).map (Icc (0 : ℝ) 1)) ∧
      (∀ i j, i.2 = j.2 → EqOn ((face i).boundary 1).map
        ((face j).boundary 1).map (Icc (0 : ℝ) 1)) ∧
      (∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
        (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        convexHull ℝ (range b) ⊆ C.source ∧
        (face i).carrier = C '' convexHull ℝ (range b) ∧
        ∀ k, ((face i).boundary k).map = C ∘
          affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) := by
  classical
  let J (i : Bool × Bool) := (sectorParameterEquiv 0 i).toOpenPartialHomeomorph.trans H
  have hJ0 (i : Bool × Bool) : (0 : ℝ × ℝ) ∈ (J i).source := by
    refine ⟨mem_univ _, ?_⟩
    change sectorParameterEquiv 0 i 0 ∈ H.source
    simpa only [sectorParameterEquiv_zero] using h0
  have hJ (i : Bool × Bool) : ContDiffOn ℝ ∞ (J i) (J i).source :=
    hH.comp (contDiff_sectorParameterEquiv 0 i).contDiffOn (fun _ hz => hz.2)
  have hJi (i : Bool × Bool) : ContDiffOn ℝ ∞ (J i).symm (J i).target :=
    (contDiff_sectorParameterEquiv_symm 0 i).comp_contDiffOn
      (hHi.mono (fun _ hz => hz.1))
  choose rho hrho hcaps using fun i =>
    m64Intrinsic_exists_corner_faces_at_scale (J i) (hJ0 i) (hJ i) (hJi i)
  let mu := Finset.univ.inf' Finset.univ_nonempty rho
  have hmu : 0 < mu := by simpa [mu] using hrho
  have hmule (i : Bool × Bool) : mu ≤ rho i := Finset.inf'_le rho (Finset.mem_univ i)
  let r := min (mu / 2) (T / 2)
  have hr : 0 < r := lt_min (half_pos hmu) (half_pos hT)
  have hrT : r ≤ T := (min_le_right _ _).trans (half_le_self hT.le)
  have hrho' (i : Bool × Bool) : r < rho i :=
    ((min_le_left _ _).trans_lt (half_lt_self hmu)).trans_le (hmule i)
  choose face V hsub hsecond hfirst hchord hne hV hVp hVt hcover hcoordinates using
    fun i => hcaps i r hr (hrho' i)
  let W := ⋂ i, V i
  have hW : IsOpen W := isOpen_iInter_of_finite hV
  have hWp : H 0 ∈ W := by
    apply mem_iInter.mpr
    intro i
    simpa only [J, OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      sectorParameterEquiv_zero] using hVp i
  have hWV (i : Bool × Bool) : W ⊆ V i := iInter_subset _ i
  have hWt : W ⊆ H.target := fun _ hz => (hVt (true, true) (hWV _ hz)).1
  have hsector (i : Bool × Bool) :
      J i '' ((J i).source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) =
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
    ext z
    constructor
    · rintro ⟨q, ⟨hq, hqpos⟩, rfl⟩
      exact ⟨sectorParameterEquiv 0 i q, ⟨hq.2, q, hqpos, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨hq, ⟨p, hp, rfl⟩⟩, rfl⟩
      exact ⟨p, ⟨⟨mem_univ _, hq⟩, hp⟩, rfl⟩
  refine ⟨r, face, W, hr, hrT, hW, hWp, hWt, ?_, ?_, hsecond, hfirst, hchord, hne,
    ?_, ?_, hcoordinates⟩
  · intro i
    simpa only [hsector i] using hsub i
  · intro i z hz
    apply hcover i
    exact ⟨hWV i hz.1, (hsector i).symm ▸ hz.2⟩
  · intro i j hij t ht
    rw [hfirst i t ht, hfirst j t ht]
    change H (sectorParameterEquiv 0 i (t * r, 0)) =
      H (sectorParameterEquiv 0 j (t * r, 0))
    simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]
  · intro i j hij t ht
    rw [hsecond i t ht, hsecond j t ht]
    change H (sectorParameterEquiv 0 i (0, t * r)) =
      H (sectorParameterEquiv 0 j (0, t * r))
    simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]

end PoincareConjecture
